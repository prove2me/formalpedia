-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_exp_le_one
-- name    : BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:17:07.747175+00:00
-- url     : https://prove2.me/theorems/2a609d5e-6be9-411b-bc49-3e40844203ee
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one` {A : E →L[ℂ] E} (h : NumReLE A 0) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A)‖ ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one` {A : E →L[ℂ] E} (h : NumReLE A 0) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A)‖ ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one {A : E →L[ℂ] E} (h : NumReLE A 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ 1 := by sorry
