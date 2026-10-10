-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_le_two_mul_of_numRadiusLE
-- name    : BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:52.014982+00:00
-- url     : https://prove2.me/theorems/2cc17764-e484-4cdb-ba46-06fe3a41e789
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) : ‖A‖ ≤ 2 * r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) : ‖A‖ ≤ 2 * r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r)
    (h : NumRadiusLE A r) : ‖A‖ ≤ 2 * r := by sorry
