-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_shiftEquiv_apply
-- name    : BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:37:44.743211+00:00
-- url     : https://prove2.me/theorems/56ab03b1-18ce-41cf-b23d-4a6816ec9523
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) (x : E) : shiftEquiv h hz x = (z • (1 : E →L[ℂ] E) - A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) (x : E) : shiftEquiv h hz x = (z • (1 : E →L[ℂ] E) - A) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.shiftEquiv_apply {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re)
    (x : E) : shiftEquiv h hz x = (z • (1 : E →L[ℂ] E) - A) x := by sorry
