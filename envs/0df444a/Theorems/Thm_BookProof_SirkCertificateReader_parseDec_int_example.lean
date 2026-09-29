-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_parseDec_int_example
-- name    : BookProof.SirkCertificateReader.parseDec_int_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:13:23.341989+00:00
-- url     : https://prove2.me/theorems/b8282d8f-8188-4b0d-a3a8-0bc630c30627
-- title:
--   : parseDec "7".toList = some ⟨7, 0⟩
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.parseDec_int_example` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.parseDec_int_example
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.parseDec_int_example : parseDec "7".toList = some ⟨7, 0⟩ := by sorry
