-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_pow_le_of_numRadiusLE
-- name    : BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:01.214778+00:00
-- url     : https://prove2.me/theorems/051515bb-21a8-4c28-86b8-f85cd7353641
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ) (hn : 0 < n) : ‖A ^ n‖ ≤ 2 * r ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ) (hn : 0 < n) : ‖A ^ n‖ ≤ 2 * r ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.norm_pow_le_of_numRadiusLE {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r)
    (h : NumRadiusLE A r) (n : ℕ) (hn : 0 < n) : ‖A ^ n‖ ≤ 2 * r ^ n := by sorry
