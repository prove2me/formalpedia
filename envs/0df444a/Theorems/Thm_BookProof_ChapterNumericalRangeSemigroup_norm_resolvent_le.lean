-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_resolvent_le
-- name    : BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:38:07.595344+00:00
-- url     : https://prove2.me/theorems/412a4ce5-6938-481b-9c2d-bbed11d2182e
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) : ‖((shiftEquiv h hz).symm : E →L[ℂ] E)‖ ≤...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le` {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) : ‖((shiftEquiv h hz).symm : E →L[ℂ] E)‖ ≤ (z.re - ω)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le {A : E →L[ℂ] E} {ω : ℝ} (h : NumReLE A ω) {z : ℂ} (hz : ω < z.re) :
    ‖((shiftEquiv h hz).symm : E →L[ℂ] E)‖ ≤ (z.re - ω)⁻¹ := by sorry
