-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_Decimal_toQ_nonneg
-- name    : BookProof.SirkCertificateReader.Decimal.toQ_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:09:49.141783+00:00
-- url     : https://prove2.me/theorems/58c26e19-fe2e-49f4-b7d0-ba30e1d58413
-- title:
--   {d : Decimal} (h : 0 ≤ d.mant) : 0 ≤ d.toQ
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.Decimal.toQ_nonneg` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.Decimal.toQ_nonneg
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader
open BookProof.SirkCertificateReader.Decimal









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.Decimal.toQ_nonneg {d : Decimal} (h : 0 ≤ d.mant) : 0 ≤ d.toQ := by sorry
