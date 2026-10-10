-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_exp_le
-- name    : BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:43.202048+00:00
-- url     : https://prove2.me/theorems/c3a7ebf2-99dd-4f60-a644-ddbe39c728ca
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (ω * t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (ω * t)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.norm_exp_le`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_le {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A)‖ ≤ Real.exp (ω * t) := by sorry
