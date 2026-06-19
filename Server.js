// server.js

const express = require("express");
const multer = require("multer");
const path = require("path");
const fs = require("fs");
const crypto = require("crypto");
const QRCode = require("qrcode");
const session = require("express-session");
const nodemailer = require("nodemailer");
const dotenv = require("dotenv").config();



const app = express();

app.set("trust proxy", true);

const PORT = process.env.PORT || 3000;

const UPLOAD_DIR = path.join(__dirname, "uploads");
const DB_PATH = path.join(__dirname, "db.json");
const AUDIT_LOG_PATH = path.join(__dirname, "audit.log");

const ADMIN_USER = process.env.ADMIN_USER;
const ADMIN_EMAIL = process.env.ADMIN_EMAIL;
const ADMIN_PASS = process.env.ADMIN_PASS;

const SESSION_SECRET = process.env.SESSION_SECRET || "change-this-session-secret";

// Set COOKIE_SECURE=true when running behind HTTPS in production.
const COOKIE_SECURE = process.env.COOKIE_SECURE === "true";

const MAX_FILE_MB = Number(process.env.MAX_FILE_MB || 50);

const MAX_TITLE_LEN = 200;
const MAX_CATEGORY_LEN = 100;

// Allow-list of accepted upload types.
const ALLOWED_MIME_TO_EXT = {
  "application/pdf": [".pdf"],
  "image/png": [".png"],
  "image/jpeg": [".jpg", ".jpeg"],
  "image/gif": [".gif"],
  "image/webp": [".webp"],
  "text/plain": [".txt"],
  "text/csv": [".csv"],
  "application/json": [".json"],
  "video/mp4": [".mp4"],
  "audio/mpeg": [".mp3"],
  "audio/wav": [".wav"],
  "audio/x-wav": [".wav"],
  "application/msword": [".doc"],
  "application/vnd.openxmlformats-officedocument.wordprocessingml.document": [".docx"],
  "application/vnd.ms-excel": [".xls"],
  "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet": [".xlsx"],
  "application/zip": [".zip"]
};

const ALL_ALLOWED_EXT = new Set(Object.values(ALLOWED_MIME_TO_EXT).flat());

const PREVIEWABLE_IMAGE_EXT = new Set([".png", ".jpg", ".jpeg", ".gif", ".webp"]);
const PREVIEWABLE_TEXT_EXT = new Set([".txt", ".csv", ".json"]);
const PREVIEWABLE_PDF_EXT = new Set([".pdf"]);
const PREVIEWABLE_AUDIO_EXT = new Set([".mp3", ".wav"]);
const PREVIEWABLE_VIDEO_EXT = new Set([".mp4"]);

const TEXT_PREVIEW_MAX_BYTES = 64 * 1024; // only read first 64KB for text preview

if (!fs.existsSync(UPLOAD_DIR)) {
  fs.mkdirSync(UPLOAD_DIR, { recursive: true });
}

app.use(express.urlencoded({ extended: true, limit: "1mb" }));

app.use(
  session({
    secret: SESSION_SECRET,
    resave: false,
    saveUninitialized: false,
    cookie: {
      httpOnly: true,
      sameSite: "lax",
      secure: COOKIE_SECURE,
      maxAge: 12 * 60 * 60 * 1000 // 12 hours
    }
  })
);

function auditLog(req, action, details = {}) {
  const entry = {
    time: new Date().toISOString(),
    action,
    ip: req.ip,
    username: (req.session && req.session.username) || null,
    ...details
  };

  try {
    fs.appendFileSync(AUDIT_LOG_PATH, JSON.stringify(entry) + "\n");
  } catch (err) {
    console.error("Failed to write audit log:", err.message);
  }
}

function makeRateLimiter({ windowMs, max }) {
  const hits = new Map();

  return function rateLimiter(req, res, next) {
    const now = Date.now();
    const ip = req.ip || "unknown";
    const timestamps = (hits.get(ip) || []).filter(t => now - t < windowMs);

    if (timestamps.length >= max) {
      auditLog(req, "rate_limited", { path: req.path });
      return res.status(429).send("Too many requests. Please wait and try again.");
    }

    timestamps.push(now);
    hits.set(ip, timestamps);
    next();
  };
}

const loginLimiter = makeRateLimiter({ windowMs: 15 * 60 * 1000, max: 10 });
const resetLimiter = makeRateLimiter({ windowMs: 15 * 60 * 1000, max: 5 });
const uploadLimiter = makeRateLimiter({ windowMs: 60 * 1000, max: 20 });

const CSRF_COOKIE_NAME = "csrfToken";

function parseCookies(req) {
  const header = req.headers.cookie;
  const out = {};
  if (!header) return out;

  for (const part of header.split(";")) {
    const idx = part.indexOf("=");
    if (idx === -1) continue;
    const key = part.slice(0, idx).trim();
    const val = part.slice(idx + 1).trim();
    out[key] = decodeURIComponent(val);
  }
  return out;
}

function ensureCsrfCookie(req, res) {
  const cookies = parseCookies(req);
  let token = cookies[CSRF_COOKIE_NAME];

  if (!token) {
    token = crypto.randomBytes(24).toString("hex");
    res.setHeader(
      "Set-Cookie",
      `${CSRF_COOKIE_NAME}=${encodeURIComponent(token)}; Path=/; SameSite=Lax${COOKIE_SECURE ? "; Secure" : ""}`
    );
  }

  req.csrfToken = token;
  return token;
}

app.use(function (req, res, next) {
  ensureCsrfCookie(req, res);
  next();
});

function csrfField(req) {
  return `<input type="hidden" name="_csrf" value="${escapeHtml(req.csrfToken)}">`;
}

function verifyCsrf(req) {
  const cookies = parseCookies(req);
  const cookieToken = cookies[CSRF_COOKIE_NAME];
  const bodyToken = req.body && req.body._csrf;

  return (
    typeof cookieToken === "string" &&
    typeof bodyToken === "string" &&
    cookieToken.length > 0 &&
    crypto.timingSafeEqual(
      Buffer.from(cookieToken.padEnd(64, "0")),
      Buffer.from(bodyToken.padEnd(64, "0"))
    ) &&
    cookieToken === bodyToken
  );
}

function hashValue(value, salt = crypto.randomBytes(16).toString("hex")) {
  const hash = crypto.scryptSync(value, salt, 64).toString("hex");
  return `${salt}:${hash}`;
}

function verifyValue(value, storedHash) {
  if (!storedHash || !storedHash.includes(":")) return false;

  const [salt, originalHash] = storedHash.split(":");
  const testHash = crypto.scryptSync(value, salt, 64);

  if (testHash.length !== Buffer.from(originalHash, "hex").length) return false;

  return crypto.timingSafeEqual(Buffer.from(originalHash, "hex"), testHash);
}

const DEFAULT_DB = () => ({
  admin: {
    username: ADMIN_USER,
    email: ADMIN_EMAIL,
    passwordHash: hashValue(ADMIN_PASS)
  },
  categories: [],
  files: [],
  reset: null
});

function initDb() {
  if (!fs.existsSync(DB_PATH)) {
    fs.writeFileSync(DB_PATH, JSON.stringify(DEFAULT_DB(), null, 2));
    return;
  }

  let db;
  try {
    db = JSON.parse(fs.readFileSync(DB_PATH, "utf8"));
  } catch (err) {
    console.error("db.json was corrupt/unreadable, recreating it:", err.message);
    fs.writeFileSync(DB_PATH, JSON.stringify(DEFAULT_DB(), null, 2));
    return;
  }

  const defaults = DEFAULT_DB();
  let changed = false;

  if (!db.admin) { db.admin = defaults.admin; changed = true; }
  if (!Array.isArray(db.categories)) { db.categories = []; changed = true; }
  if (!Array.isArray(db.files)) { db.files = []; changed = true; }
  if (!("reset" in db)) { db.reset = null; changed = true; }

  if (changed) {
    fs.writeFileSync(DB_PATH, JSON.stringify(db, null, 2));
  }
}

function readDb() {
  initDb();
  return JSON.parse(fs.readFileSync(DB_PATH, "utf8"));
}

function writeDb(db) {
  fs.writeFileSync(DB_PATH, JSON.stringify(db, null, 2));
}

function slugify(value) {
  return String(value)
    .toLowerCase()
    .trim()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "");
}

function safeFilename(value) {
  return String(value).replace(/[^a-zA-Z0-9.\-_]/g, "_");
}

function escapeHtml(value) {
  return String(value || "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function getHost(req) {
  return `${req.protocol}://${req.get("host")}`;
}

function findFile(db, id) {
  return db.files.find(f => f.id === id);
}

function isValidEmail(value) {
  return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(value);
}

function validateUploadType(originalname, mimetype) {
  const ext = path.extname(originalname).toLowerCase();

  if (!ext || !ALL_ALLOWED_EXT.has(ext)) {
    return { ok: false, reason: `File type "${ext || "unknown"}" is not allowed.` };
  }

  const allowedExtsForMime = ALLOWED_MIME_TO_EXT[mimetype];
  if (!allowedExtsForMime || !allowedExtsForMime.includes(ext)) {
    return {
      ok: false,
      reason: `File extension "${ext}" does not match declared type "${mimetype}".`
    };
  }

  return { ok: true, ext };
}

function previewKind(ext) {
  if (PREVIEWABLE_IMAGE_EXT.has(ext)) return "image";
  if (PREVIEWABLE_PDF_EXT.has(ext)) return "pdf";
  if (PREVIEWABLE_TEXT_EXT.has(ext)) return "text";
  if (PREVIEWABLE_AUDIO_EXT.has(ext)) return "audio";
  if (PREVIEWABLE_VIDEO_EXT.has(ext)) return "video";
  return "none";
}

async function sendOtpEmail(to, otp) {
  const hasSmtp = process.env.SMTP_HOST && process.env.SMTP_USER && process.env.SMTP_PASS;

  if (!hasSmtp) {
    console.log("====================================");
    console.log("PASSWORD RESET OTP:", otp);
    console.log("SMTP not configured. OTP printed here.");
    console.log("====================================");
    return;
  }

  const transporter = nodemailer.createTransport({
    host: process.env.SMTP_HOST,
    port: Number(process.env.SMTP_PORT || 587),
    secure: process.env.SMTP_SECURE === "true",
    auth: {
      user: process.env.SMTP_USER,
      pass: process.env.SMTP_PASS
    }
  });

  await transporter.sendMail({
    from: process.env.SMTP_FROM || process.env.SMTP_USER,
    to,
    subject: "Admin password reset OTP",
    text: `Your password reset OTP is: ${otp}\n\nThis code expires in 10 minutes.`
  });
}

const dynamicStorage = multer.diskStorage({
  destination: function (req, file, cb) {
    cb(null, UPLOAD_DIR);
  },
  filename: function (req, file, cb) {
    if (req.body.action === "replace") {
      const db = readDb();
      const existing = findFile(db, req.body.id);
      if (!existing) {
        return cb(new Error("File not found for replace."));
      }
      return cb(null, existing.storedName);
    }

    const category = slugify(req.body.category || "uncategorized");
    const title = slugify(req.body.title || "file");
    const ext = path.extname(file.originalname).toLowerCase() || ".bin";
    const storedName = safeFilename(`${category}_${title}_${Date.now()}${ext}`);

    cb(null, storedName);
  }
});

const dynamicUpload = multer({
  storage: dynamicStorage,
  limits: {
    fileSize: MAX_FILE_MB * 1024 * 1024,
    files: 1
  },
  fileFilter: function (req, file, cb) {
    const result = validateUploadType(file.originalname, file.mimetype);
    if (!result.ok) {
      return cb(new Error(result.reason));
    }
    cb(null, true);
  }
}).single("file");

function page(title, body, extraHead = "") {
  return `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>${escapeHtml(title)}</title>
  <style>
    :root {
      --bg: #f4f5f7;
      --surface: #ffffff;
      --border: #e1e4e8;
      --text: #1f2328;
      --muted: #6a7280;
      --accent: #2563eb;
      --accent-dark: #1d4ed8;
      --danger: #b00020;
      --danger-dark: #8e001a;
      --notice: #1a5d1a;
      --radius: 10px;
    }

    * { box-sizing: border-box; }

    body {
      font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
      max-width: 1000px;
      margin: 0 auto;
      padding: 0 1rem 3rem;
      color: var(--text);
      background: var(--bg);
    }

    h1, h2 { margin: 0; }

    input, button, select {
      font-size: 1rem;
      padding: 0.5rem 0.7rem;
      border: 1px solid var(--border);
      border-radius: 6px;
      font-family: inherit;
    }

    input:focus, button:focus, select:focus {
      outline: 2px solid var(--accent);
      outline-offset: 1px;
    }

    button {
      cursor: pointer;
      background: var(--accent);
      color: #fff;
      border: none;
      font-weight: 600;
    }

    button:hover { background: var(--accent-dark); }

    button[type="button"] {
      background: var(--surface);
      color: var(--text);
      border: 1px solid var(--border);
      font-weight: 500;
    }

    button[type="button"]:hover { background: #f0f1f3; }

    .error { color: var(--danger); }
    .notice { color: var(--notice); }

    .topbar {
      display: flex;
      align-items: center;
      justify-content: space-between;
      padding: 1.25rem 0;
      flex-wrap: wrap;
      gap: 0.75rem;
    }

    .topbar h1 { font-size: 1.4rem; }

    .panel {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: var(--radius);
      padding: 1.25rem 1.5rem;
      margin-bottom: 1.25rem;
      box-shadow: 0 1px 2px rgba(0,0,0,0.04);
    }

    .panel > legend, fieldset.panel > legend {
      font-weight: 700;
      font-size: 1.05rem;
      padding: 0 0.3rem;
    }

    fieldset.panel { border: 1px solid var(--border); }

    .form-grid {
      display: grid;
      gap: 0.85rem;
      margin-top: 0.75rem;
    }

    .form-grid label {
      display: block;
      font-size: 0.85rem;
      font-weight: 600;
      color: var(--muted);
      margin-bottom: 0.3rem;
    }

    .form-grid input, .form-grid select {
      width: 100%;
    }

    .field-row { display: flex; align-items: center; gap: 0.5rem; }

    .danger { background: var(--danger); }
    .danger:hover { background: var(--danger-dark); }

    .search-bar {
      position: sticky;
      top: 0;
      background: var(--bg);
      padding: 0.75rem 0;
      z-index: 5;
      display: flex;
      gap: 0.6rem;
      align-items: center;
    }

    .search-bar input {
      flex: 1;
      padding: 0.6rem 0.9rem;
      border-radius: 8px;
      font-size: 1rem;
    }

    .search-count {
      color: var(--muted);
      font-size: 0.9rem;
      white-space: nowrap;
    }

    .file-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(280px, 1fr));
      gap: 1rem;
      margin-top: 1rem;
    }

    .file-card {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: var(--radius);
      padding: 1rem 1.1rem;
      display: flex;
      flex-direction: column;
      gap: 0.4rem;
      box-shadow: 0 1px 2px rgba(0,0,0,0.04);
    }

    .file-card .file-title {
      font-weight: 700;
      font-size: 1.05rem;
      word-break: break-word;
    }

    .file-card .file-meta {
      font-size: 0.85rem;
      color: var(--muted);
      line-height: 1.5;
    }

    .file-card .file-meta strong { color: var(--text); }

    .badge {
      display: inline-block;
      background: #e8eefc;
      color: var(--accent-dark);
      border-radius: 999px;
      padding: 0.15rem 0.6rem;
      font-size: 0.75rem;
      font-weight: 600;
      width: fit-content;
    }

    .file-card .file-link {
      font-size: 0.85rem;
      word-break: break-all;
    }

    .file-card .qr-row {
      display: flex;
      align-items: center;
      gap: 0.75rem;
      margin-top: 0.2rem;
    }

    .file-card .qr-row img {
      width: 64px;
      height: 64px;
      border: 1px solid var(--border);
      border-radius: 6px;
    }

    .file-card .file-actions {
      margin-top: auto;
      padding-top: 0.5rem;
    }

    .file-card .file-actions a {
      display: inline-block;
      font-weight: 600;
      color: var(--accent);
      text-decoration: none;
    }

    .file-card .file-actions a:hover { text-decoration: underline; }

    .empty-state {
      text-align: center;
      color: var(--muted);
      padding: 2.5rem 1rem;
    }

    .preview img, .preview video { max-width: 100%; height: auto; border-radius: 8px; }
    .preview iframe { width: 100%; height: 600px; border: 1px solid var(--border); border-radius: 8px; }
    .preview pre { background: #f5f5f5; padding: 1rem; overflow: auto; max-height: 400px; white-space: pre-wrap; word-break: break-word; border-radius: 8px; }

    .detail-meta {
      background: var(--surface);
      border: 1px solid var(--border);
      border-radius: var(--radius);
      padding: 1rem 1.25rem;
      font-size: 0.9rem;
      line-height: 1.6;
    }

    .back-link { display: inline-block; margin-bottom: 1rem; color: var(--accent); text-decoration: none; font-weight: 600; }
    .back-link:hover { text-decoration: underline; }

    fieldset { margin-bottom: 1.5rem; }
  </style>
  ${extraHead}
</head>
<body>
  ${body}
</body>
</html>
`;
}

function passwordFieldWithToggle(name, idSuffix) {
  const inputId = `pw_${idSuffix}`;
  return `
    <span class="field-row">
      <input id="${inputId}" name="${name}" type="password" autocomplete="off">
      <button type="button" onclick="
        const el = document.getElementById('${inputId}');
        el.type = el.type === 'password' ? 'text' : 'password';
        this.textContent = el.type === 'password' ? 'Show' : 'Hide';
      ">Show</button>
    </span>
  `;
}

function renderLoginPage(req, message = "", isError = true) {
  return page(
    "Admin Login",
    `
    <h1>Admin Login</h1>
    ${message ? `<p class="${isError ? "error" : "notice"}">${escapeHtml(message)}</p>` : ""}
    <form method="POST" action="/admin">
      ${csrfField(req)}
      <input type="hidden" name="action" value="login">
      <p>Username: <input name="username" autocomplete="username" required></p>
      <p>Password: ${passwordFieldWithToggle("password", "login")}</p>
      <button type="submit">Login</button>
    </form>
    <hr>
    <form method="POST" action="/admin">
      ${csrfField(req)}
      <input type="hidden" name="action" value="show_forgot">
      <button type="submit">Forgot password?</button>
    </form>
    `
  );
}

function renderForgotPage(req, message = "") {
  return page(
    "Forgot Password",
    `
    <h1>Reset Admin Password</h1>
    ${message ? `<p>${escapeHtml(message)}</p>` : ""}
    <form method="POST" action="/admin">
      ${csrfField(req)}
      <input type="hidden" name="action" value="request_reset">
      <p>Admin email: <input name="email" type="email" required></p>
      <button type="submit">Send OTP</button>
    </form>
    <hr>
    <form method="GET" action="/admin">
      <button type="submit">Back to login</button>
    </form>
    `
  );
}

function renderResetPage(req, message = "", email = "") {
  return page(
    "Enter OTP",
    `
    <h1>Enter OTP</h1>
    ${message ? `<p>${escapeHtml(message)}</p>` : ""}
    <form method="POST" action="/admin">
      ${csrfField(req)}
      <input type="hidden" name="action" value="reset_password">
      <p>Admin email: <input name="email" type="email" value="${escapeHtml(email)}" required></p>
      <p>OTP: <input name="otp" required></p>
      <p>New password: ${passwordFieldWithToggle("newPassword", "reset")}<br><small>At least 8 characters.</small></p>
      <button type="submit">Reset Password</button>
    </form>
    <hr>
    <form method="GET" action="/admin">
      <button type="submit">Back to login</button>
    </form>
    `
  );
}

function renderPreview(file, fileUrl) {
  const ext = path.extname(file.storedName).toLowerCase();
  const kind = previewKind(ext);

  if (kind === "image") return `<div class="preview"><img src="${fileUrl}" alt="${escapeHtml(file.title)}"></div>`;
  if (kind === "pdf") return `<div class="preview"><iframe src="${fileUrl}" title="${escapeHtml(file.title)}"></iframe></div>`;
  if (kind === "audio") return `<div class="preview"><audio controls src="${fileUrl}"></audio></div>`;
  if (kind === "video") return `<div class="preview"><video controls src="${fileUrl}"></video></div>`;

  if (kind === "text") {
    let snippet = "";
    let truncated = false;
    try {
      const filePath = path.resolve(UPLOAD_DIR, file.storedName);
      const stat = fs.statSync(filePath);
      const readLen = Math.min(stat.size, TEXT_PREVIEW_MAX_BYTES);
      const fd = fs.openSync(filePath, "r");
      const buf = Buffer.alloc(readLen);
      fs.readSync(fd, buf, 0, readLen, 0);
      fs.closeSync(fd);
      snippet = buf.toString("utf8");
      truncated = stat.size > TEXT_PREVIEW_MAX_BYTES;
    } catch (err) {
      return `<div class="preview"><p class="error">Preview unavailable: ${escapeHtml(err.message)}</p></div>`;
    }
    return `
      <div class="preview">
        <pre>${escapeHtml(snippet)}${truncated ? "\n\n... (truncated, showing first 64KB)" : ""}</pre>
      </div>
    `;
  }

  return `<div class="preview"><p>No inline preview available for this file type. Use the direct URL to download/open it.</p></div>`;
}

function renderFileDetailPage(req, file, host, message = "", isError = false) {
  const fileUrl = `${host}/files/${encodeURIComponent(file.storedName)}`;

  return page(
    `File: ${file.title}`,
    `
    <div class="topbar"><h1>File Details</h1></div>
    ${message ? `<p class="${isError ? "error" : "notice"}">${escapeHtml(message)}</p>` : ""}
    <a class="back-link" href="/admin">&laquo; Back to all files</a>

    <div class="detail-meta">
      <strong>Original name:</strong> ${escapeHtml(file.originalName)}<br>
      <strong>Stored name:</strong> ${escapeHtml(file.storedName)}<br>
      <strong>Type:</strong> ${escapeHtml(file.mimeType || "unknown")}<br>
      <strong>Size:</strong> ${file.sizeBytes} bytes<br>
      <strong>Uploaded:</strong> ${escapeHtml(file.createdAt || "")}<br>
      ${file.updatedAt ? `<strong>Last updated:</strong> ${escapeHtml(file.updatedAt)}<br>` : ""}
      <strong>Direct URL:</strong> <a href="${fileUrl}" target="_blank">${fileUrl}</a>
    </div>

    <h2 style="margin: 1.5rem 0 0.5rem;">Preview</h2>
    ${renderPreview(file, fileUrl)}

    <fieldset class="panel" style="margin-top:1.5rem;">
      <legend>Edit Details</legend>
      <form method="POST" action="/admin">
        ${csrfField(req)}
        <input type="hidden" name="action" value="edit">
        <input type="hidden" name="id" value="${escapeHtml(file.id)}">
        <div class="form-grid">
          <div>
            <label for="edit_category">Category</label>
            <input id="edit_category" name="category" value="${escapeHtml(file.category)}" maxlength="${MAX_CATEGORY_LEN}" required>
          </div>
          <div>
            <label for="edit_title">File display name</label>
            <input id="edit_title" name="title" value="${escapeHtml(file.title)}" maxlength="${MAX_TITLE_LEN}" required>
          </div>
        </div>
        <div style="margin-top:1rem;"><button type="submit">Save Changes</button></div>
      </form>
    </fieldset>

    <fieldset class="panel">
      <legend>Replace File Content</legend>
      <p class="file-meta">Uploading here keeps the same stored filename and public URL above; only the file content/type/size are updated.</p>
      <form method="POST" action="/admin" enctype="multipart/form-data">
        ${csrfField(req)}
        <input type="hidden" name="action" value="replace">
        <input type="hidden" name="id" value="${escapeHtml(file.id)}">
        <div class="form-grid">
          <div>
            <label for="replace_file">New file</label>
            <input id="replace_file" type="file" name="file" required>
          </div>
        </div>
        <div style="margin-top:1rem;"><button type="submit">Replace</button></div>
      </form>
    </fieldset>

    <fieldset class="panel">
      <legend>Delete File</legend>
      <form method="POST" action="/admin" onsubmit="return confirm('Delete this file permanently? This cannot be undone.');">
        ${csrfField(req)}
        <input type="hidden" name="action" value="delete">
        <input type="hidden" name="id" value="${escapeHtml(file.id)}">
        <button type="submit" class="danger">Delete</button>
      </form>
    </fieldset>
    `
  );
}

async function renderAdminPage(req, message = "", result = null, isError = false) {
  const db = readDb();
  const host = getHost(req);

  const categoryOptions = db.categories
    .map(cat => `<option value="${escapeHtml(cat)}"></option>`)
    .join("");

  const categoryCounts = {};
  for (const file of db.files) {
    const category = file.category || "Uncategorized";
    categoryCounts[category] = (categoryCounts[category] || 0) + 1;
  }

  const categoryFilterOptions = Object.entries(categoryCounts)
    .sort(([a], [b]) => a.localeCompare(b))
    .map(([category, count]) => {
      return `<option value="${escapeHtml(category.toLowerCase())}">${escapeHtml(category)} (${count})</option>`;
    })
    .join("");

  let filesHtml = "";

  for (const file of db.files.slice().reverse()) {
    const fileUrl = `${host}/files/${encodeURIComponent(file.storedName)}`;
    const qrDataUrl = await QRCode.toDataURL(fileUrl);
    const detailUrl = `/admin/file/${encodeURIComponent(file.id)}`;

    // Fix: Properly double-escape or remove raw double quotes to safely stringify inside standard dataset elements
    const searchKey = escapeHtml(
      [file.title, file.category, file.originalName, file.storedName]
        .join(" ")
        .toLowerCase()
    );
    const fileCategoryLower = escapeHtml((file.category || "").toLowerCase());

    filesHtml += `
      <div class="file-card" data-search="${searchKey}" data-category="${fileCategoryLower}">
        <div class="file-title">${escapeHtml(file.title)}</div>
        <span class="badge">${escapeHtml(file.category)}</span>
        <div class="file-meta">
          <strong>Original:</strong> ${escapeHtml(file.originalName)}<br>
          <strong>Stored:</strong> ${escapeHtml(file.storedName)}<br>
          <strong>Type:</strong> ${escapeHtml(file.mimeType || "unknown")}<br>
          <strong>Size:</strong> ${file.sizeBytes} bytes
        </div>
        <div class="file-link"><a href="${fileUrl}" target="_blank">${fileUrl}</a></div>
        <div class="qr-row">
          <img src="${qrDataUrl}" alt="QR code for ${escapeHtml(file.title)}">
          <a href="${detailUrl}" style="font-weight:600;">View / Edit / Replace / Delete</a>
        </div>
      </div>
    `;
  }

  const resultHtml = result
    ? `
      <div class="panel">
        <h2 style="margin-bottom:0.75rem;">Uploaded</h2>
        <div class="file-meta" style="margin-bottom:0.75rem;"><strong>Stored filename:</strong> ${escapeHtml(result.storedName)}</div>
        <div class="file-link" style="margin-bottom:0.75rem;"><strong>Direct file URL:</strong><br><a href="${result.fileUrl}" target="_blank">${result.fileUrl}</a></div>
        <img src="${result.qrDataUrl}">
      </div>
    `
    : "";

  return page(
    "Admin Upload",
    `
    <div class="topbar">
      <h1>Admin Upload</h1>
      <form method="POST" action="/admin">
        ${csrfField(req)}
        <input type="hidden" name="action" value="logout">
        <button type="submit">Logout</button>
      </form>
    </div>

    ${message ? `<p class="${isError ? "error" : "notice"}">${escapeHtml(message)}</p>` : ""}

    <fieldset class="panel">
      <legend>Upload File</legend>
      <form method="POST" action="/admin" enctype="multipart/form-data">
        ${csrfField(req)}
        <input type="hidden" name="action" value="upload">
        <div class="form-grid">
          <div>
            <label for="upload_category">Category</label>
            <input id="upload_category" name="category" list="categories" placeholder="reports" maxlength="${MAX_CATEGORY_LEN}" required>
            <datalist id="categories">${categoryOptions}</datalist>
          </div>
          <div>
            <label for="upload_title">File display name</label>
            <input id="upload_title" name="title" placeholder="q1 sales report" maxlength="${MAX_TITLE_LEN}" required>
          </div>
          <div>
            <label for="upload_file">File</label>
            <input id="upload_file" type="file" name="file" required>
          </div>
        </div>
        <div style="margin-top:1rem;"><button type="submit">Upload</button></div>
      </form>
    </fieldset>

    ${resultHtml}

    <div class="topbar" style="padding-bottom:0;">
      <h2>Existing Files</h2>
      <span class="search-count" id="fileCount"></span>
    </div>

    <div class="search-bar">
      <input type="search" id="fileSearch" placeholder="Search title, filename, category..." autocomplete="off" oninput="filterFiles()">
      <select id="categoryFilter" onchange="filterFiles()">
        <option value="">All categories</option>
        ${categoryFilterOptions}
      </select>
      <button type="button" onclick="clearFileFilters()">Clear</button>
    </div>

    <div class="file-grid" id="fileGrid">${filesHtml}</div>
    <div class="empty-state" id="emptyState" style="display:none;">No files match your search.</div>
    ${db.files.length === 0 ? `<div class="empty-state" id="noFilesYet">No files uploaded yet.</div>` : ""}

    <script>
      function filterFiles() {
        const query = document.getElementById('fileSearch').value.trim().toLowerCase();
        const selectedCat = document.getElementById('categoryFilter').value;
        const cards = document.querySelectorAll('#fileGrid .file-card');
        let visibleCount = 0;

        cards.forEach(function (card) {
          const haystack = card.getAttribute('data-search') || '';
          const cardCat = card.getAttribute('data-category') || '';
          
          const textMatches = haystack.indexOf(query) !== -1;
          const catMatches = !selectedCat || cardCat === selectedCat;
          const shouldShow = textMatches && catMatches;

          card.style.display = shouldShow ? '' : 'none';
          if (shouldShow) visibleCount++;
        });

        const countEl = document.getElementById('fileCount');
        if (countEl) {
          countEl.textContent = (query || selectedCat)
            ? visibleCount + ' of ' + cards.length + ' files'
            : cards.length + ' file' + (cards.length === 1 ? '' : 's');
        }

        const emptyState = document.getElementById('emptyState');
        if (emptyState) {
          emptyState.style.display = (cards.length > 0 && visibleCount === 0) ? '' : 'none';
        }
      }

      function clearFileFilters() {
        document.getElementById('fileSearch').value = '';
        document.getElementById('categoryFilter').value = '';
        filterFiles();
      }

      document.addEventListener('DOMContentLoaded', filterFiles);
    </script>
    `
  );
}

app.get("/admin", async function (req, res) {
  if (!req.session.isAdmin) {
    return res.send(renderLoginPage(req));
  }
  res.setHeader("X-Content-Type-Options", "nosniff");
  return res.send(await renderAdminPage(req));
});

app.get("/admin/file/:id", function (req, res) {
  if (!req.session.isAdmin) {
    return res.send(renderLoginPage(req));
  }

  const db = readDb();
  const file = findFile(db, req.params.id);

  if (!file) {
    return res.status(404).send(page("Not Found", "<p>File not found.</p><p><a href=\"/admin\">Back</a></p>"));
  }

  res.setHeader("X-Content-Type-Options", "nosniff");
  return res.send(renderFileDetailPage(req, file, getHost(req)));
});

app.post("/admin", function (req, res, next) {
  const contentType = req.headers["content-type"] || "";

  if (contentType.startsWith("multipart/form-data")) {
    if (!req.session.isAdmin) {
      return res.status(401).send(renderLoginPage(req, "Log in first."));
    }
    return uploadLimiter(req, res, () => handleMultipart(req, res));
  }

  return handleAdminFormPost(req, res);
});

function handleMultipart(req, res) {
  dynamicUpload(req, res, async function (err) {
    if (!verifyCsrf(req)) {
      auditLog(req, "csrf_rejected", { path: req.path });
      return res.status(403).send(page("Forbidden", "<p>Invalid or missing security token. Please go back and try again.</p><p><a href=\"/admin\">Back</a></p>"));
    }

    if (err) {
      auditLog(req, "upload_error", { message: err.message });
      return res.send(await renderAdminPage(req, err.message, null, true));
    }

    const action = req.body.action;

    if (action === "replace") {
      const db = readDb();
      const file = findFile(db, req.body.id);

      if (!file) {
        return res.status(404).send(page("Not Found", "<p>File not found.</p><p><a href=\"/admin\">Back</a></p>"));
      }

      if (!req.file) {
        return res.send(renderFileDetailPage(req, file, getHost(req), "No file selected.", true));
      }

      file.originalName = req.file.originalname;
      file.mimeType = req.file.mimetype;
      file.sizeBytes = req.file.size;
      file.updatedAt = new Date().toISOString();

      writeDb(db);
      auditLog(req, "file_replace", { fileId: file.id, storedName: file.storedName });

      return res.send(renderFileDetailPage(req, file, getHost(req), "File replaced successfully."));
    }

    if (!req.file) {
      return res.send(await renderAdminPage(req, "No file uploaded.", null, true));
    }

    const title = (req.body.title || "").trim().slice(0, MAX_TITLE_LEN) || "Untitled File";
    const category = (req.body.category || "").trim().slice(0, MAX_CATEGORY_LEN) || "Uncategorized";

    const db = readDb();

    if (!db.categories.includes(category)) {
      db.categories.push(category);
    }

    const host = getHost(req);
    const fileUrl = `${host}/files/${encodeURIComponent(req.file.filename)}`;
    const qrDataUrl = await QRCode.toDataURL(fileUrl);

    const fileRecord = {
      id: crypto.randomUUID(),
      title,
      category,
      originalName: req.file.originalname,
      storedName: req.file.filename,
      mimeType: req.file.mimetype,
      sizeBytes: req.file.size,
      createdAt: new Date().toISOString()
    };

    db.files.push(fileRecord);
    writeDb(db);
    auditLog(req, "file_upload", { fileId: fileRecord.id, storedName: fileRecord.storedName, title, category });

    return res.send(
      await renderAdminPage(req, "Upload successful.", {
        storedName: req.file.filename,
        fileUrl,
        qrDataUrl
      })
    );
  });
}

async function handleAdminFormPost(req, res) {
  const action = req.body.action;

  if (action !== "show_forgot" && !verifyCsrf(req)) {
    auditLog(req, "csrf_rejected", { path: req.path, action });
    return res.status(403).send(page("Forbidden", "<p>Invalid or missing security token. Please go back and try again.</p><p><a href=\"/admin\">Back</a></p>"));
  }

  const db = readDb();

  if (action === "login") {
    return loginLimiter(req, res, function () {
      const username = (req.body.username || "").trim();
      const password = req.body.password || "";

      const validUsername = username === db.admin.username;
      const validPassword = verifyValue(password, db.admin.passwordHash);

      if (!validUsername || !validPassword) {
        auditLog(req, "login_failed", { username });
        return res.status(401).send(renderLoginPage(req, "Invalid login."));
      }

      req.session.regenerate(function (err) {
        if (err) {
          console.error("Session regenerate failed:", err.message);
          return res.status(500).send(renderLoginPage(req, "Something went wrong. Try again."));
        }

        req.session.isAdmin = true;
        req.session.username = username;
        auditLog(req, "login_success", { username });
        return res.redirect("/admin");
      });
    });
  }

  if (action === "logout") {
    auditLog(req, "logout");
    req.session.destroy(function () {
      return res.redirect("/admin");
    });
    return;
  }

  if (action === "show_forgot") {
    return res.send(renderForgotPage(req));
  }

  if (action === "request_reset") {
    return resetLimiter(req, res, async function () {
      const email = (req.body.email || "").trim();

      if (!isValidEmail(email)) {
        return res.send(renderResetPage(req, "Please enter a valid email address.", email));
      }

      if (email === db.admin.email) {
        const otp = crypto.randomInt(100000, 1000000).toString();

        db.reset = {
          email,
          otpHash: hashValue(otp),
          expiresAt: Date.now() + 10 * 60 * 1000,
          attempts: 0
        };

        writeDb(db);
        auditLog(req, "password_reset_requested", { email });

        try {
          await sendOtpEmail(email, otp);
        } catch (err) {
          console.error("Email failed:", err.message);
          console.log("Fallback OTP:", otp);
        }
      }

      return res.send(renderResetPage(req, "If that email matches the admin account, an OTP was sent.", email));
    });
  }

  if (action === "reset_password") {
    const email = (req.body.email || "").trim();
    const otp = (req.body.otp || "").trim();
    const newPassword = req.body.newPassword || "";

    if (!newPassword || newPassword.length < 8) {
      return res.send(renderResetPage(req, "New password must be at least 8 characters.", email));
    }

    const reset = db.reset;

    if (reset && reset.email === email) {
      reset.attempts = (reset.attempts || 0) + 1;

      if (reset.attempts > 5) {
        db.reset = null;
        writeDb(db);
        auditLog(req, "password_reset_locked", { email });
        return res.send(renderResetPage(req, "Too many incorrect attempts. Please request a new OTP.", email));
      }
      writeDb(db);
    }

    const validReset =
      reset &&
      reset.email === email &&
      Date.now() <= reset.expiresAt &&
      verifyValue(otp, reset.otpHash);

    if (!validReset) {
      return res.send(renderResetPage(req, "Invalid or expired OTP.", email));
    }

    db.admin.passwordHash = hashValue(newPassword);
    db.reset = null;
    writeDb(db);
    auditLog(req, "password_reset_success", { email });

    return res.send(renderLoginPage(req, "Password reset successful. Log in.", false));
  }

  if (action === "edit") {
    if (!req.session.isAdmin) {
      return res.status(401).send(renderLoginPage(req, "Log in first."));
    }

    const file = findFile(db, req.body.id);
    if (!file) {
      return res.status(404).send(page("Not Found", "<p>File not found.</p><p><a href=\"/admin\">Back</a></p>"));
    }

    const newTitle = (req.body.title || "").trim().slice(0, MAX_TITLE_LEN);
    const newCategory = (req.body.category || "").trim().slice(0, MAX_CATEGORY_LEN);

    if (!newTitle || !newCategory) {
      return res.send(renderFileDetailPage(req, file, getHost(req), "Title and category cannot be empty.", true));
    }

    const before = { title: file.title, category: file.category };
    file.title = newTitle;
    file.category = newCategory;

    if (!db.categories.includes(newCategory)) {
      db.categories.push(newCategory);
    }

    file.updatedAt = new Date().toISOString();
    writeDb(db);
    auditLog(req, "file_edit", { fileId: file.id, before, after: { title: newTitle, category: newCategory } });

    return res.send(renderFileDetailPage(req, file, getHost(req), "Saved."));
  }

  if (action === "delete") {
    if (!req.session.isAdmin) {
      return res.status(401).send(renderLoginPage(req, "Log in first."));
    }

    const file = findFile(db, req.body.id);
    if (!file) {
      return res.status(404).send(page("Not Found", "<p>File not found.</p><p><a href=\"/admin\">Back</a></p>"));
    }

    const filePath = path.resolve(UPLOAD_DIR, file.storedName);
    if (filePath.startsWith(path.resolve(UPLOAD_DIR)) && fs.existsSync(filePath)) {
      fs.unlinkSync(filePath);
    }

    db.files = db.files.filter(f => f.id !== file.id);
    writeDb(db);
    auditLog(req, "file_delete", { fileId: file.id, storedName: file.storedName, title: file.title });

    return res.redirect("/admin");
  }

  return res.redirect("/admin");
}

app.get("/files/:filename", function (req, res) {
  const filename = req.params.filename;

  if (filename.includes("..") || filename.includes("/") || filename.includes("\\")) {
    return res.status(400).send("Invalid filename");
  }

  const filePath = path.resolve(UPLOAD_DIR, filename);

  if (!filePath.startsWith(path.resolve(UPLOAD_DIR))) {
    return res.status(400).send("Invalid path");
  }

  if (!fs.existsSync(filePath)) {
    return res.status(404).send("File not found");
  }

  res.setHeader("X-Content-Type-Options", "nosniff");

  const ext = path.extname(filename).toLowerCase();
  const inlineAllowed = new Set([
    ".pdf", ".png", ".jpg", ".jpeg", ".gif", ".webp",
    ".txt", ".csv", ".json", ".mp4", ".mp3", ".wav"
  ]);

  if (inlineAllowed.has(ext)) {
    return res.sendFile(filePath);
  }

  return res.download(filePath, filename);
});

app.get("*", (req, res) => {
  res.setHeader("X-Content-Type-Options", "nosniff");
  res.status(404).send(page("Not Found", "<p>Page not found.</p>"));
});

app.use(function (err, req, res, next) {
  console.error("Unhandled error:", err);
  auditLog(req, "unhandled_error", { message: err.message, path: req.path });

  if (res.headersSent) return next(err);

  res.status(500).send(page("Error", "<p>Something went wrong. Please try again.</p><p><a href=\"/admin\">Back to admin</a></p>"));
});

app.listen(PORT, function () {
  initDb();
  console.log(`Server running at http://localhost:${PORT}/admin`);
});