-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_formatExample_certified_gap
-- name    : BookProof.SirkCertificateReader.formatExample_certified_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:04:13.517566+00:00
-- url     : https://prove2.me/theorems/1d9414cc-a25a-414d-9bf7-c23a42d67800
-- title:
--   {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T P : E →ₗ[ℂ] E} (hEven : sectorGround T P 1 ≤ ((formatExampleData.even.theta.toQ : ℚ) : ℝ) +...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.formatExample_certified_gap` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.formatExample_certified_gap
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkCertificateReader.formatExample_certified_gap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T P : E →ₗ[ℂ] E}
    (hEven : sectorGround T P 1
        ≤ ((formatExampleData.even.theta.toQ : ℚ) : ℝ)
          + ((formatExampleData.even.delta.toQ : ℚ) : ℝ))
    (hOdd : ((formatExampleData.odd.theta.toQ : ℚ) : ℝ)
        - ((formatExampleData.odd.delta.toQ : ℚ) : ℝ) ≤ sectorGround T P (-1)) :
    (1.932 : ℝ) ≤ sectorGround T P (-1) - sectorGround T P 1
      ∧ sectorGround T P 1 < sectorGround T P (-1) := by sorry
