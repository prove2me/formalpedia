-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_parseDec_neg_example
-- name    : BookProof.SirkCertificateReader.parseDec_neg_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:49:09.277589+00:00
-- url     : https://prove2.me/theorems/e3ee22f3-7e4e-454c-a08d-b93166898e26
-- title:
--   : parseDec "-0.4231".toList = some ⟨-4231, 4⟩
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.parseDec_neg_example` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.parseDec_neg_example
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.parseDec_neg_example : parseDec "-0.4231".toList = some ⟨-4231, 4⟩ := by sorry
