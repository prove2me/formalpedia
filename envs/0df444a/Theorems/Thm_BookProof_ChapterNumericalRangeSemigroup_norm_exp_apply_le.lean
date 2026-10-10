-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_exp_apply_le
-- name    : BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:32.619218+00:00
-- url     : https://prove2.me/theorems/c52bb6e0-9a33-48ca-ae43-e3bbef78ead5
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (x : E) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A) x‖ ≤ Real.exp...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (x : E) {t : ℝ} (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A) x‖ ≤ Real.exp (ω * t) * ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) (x : E) {t : ℝ}
    (ht : 0 ≤ t) : ‖NormedSpace.exp (t • A) x‖ ≤ Real.exp (ω * t) * ‖x‖ := by sorry
