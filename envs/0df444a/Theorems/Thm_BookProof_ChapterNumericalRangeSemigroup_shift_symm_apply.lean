-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_shift_symm_apply
-- name    : BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:37:54.211632+00:00
-- url     : https://prove2.me/theorems/7c7e5639-ad74-484b-a48c-e18a5e844978
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) (y : E) : (z • (1 : E →L[ℂ] E) - A) ((shiftEquiv h hz)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) (y : E) : (z • (1 : E →L[ℂ] E) - A) ((shiftEquiv h hz).symm y) = y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re)
    (y : E) : (z • (1 : E →L[ℂ] E) - A) ((shiftEquiv h hz).symm y) = y := by sorry
