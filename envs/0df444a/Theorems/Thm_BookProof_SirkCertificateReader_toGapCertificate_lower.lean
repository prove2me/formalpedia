-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_toGapCertificate_lower
-- name    : BookProof.SirkCertificateReader.toGapCertificate_lower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:50:23.239391+00:00
-- url     : https://prove2.me/theorems/58e7fe7e-15bd-4e47-a5e3-d193fdb3afce
-- title:
--   {d : CertificateData} {c : GapCertificate} (h : d.toGapCertificate = some c) : c.lower = ((d.lowerQ : ℚ) : ℝ)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.toGapCertificate_lower` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.toGapCertificate_lower
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.toGapCertificate_lower {d : CertificateData} {c : GapCertificate}
    (h : d.toGapCertificate = some c) : c.lower = ((d.lowerQ : ℚ) : ℝ) := by sorry
