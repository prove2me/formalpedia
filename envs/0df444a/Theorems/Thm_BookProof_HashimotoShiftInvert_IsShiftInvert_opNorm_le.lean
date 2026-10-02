-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_opNorm_le
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvert.opNorm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T20:30:10.641283+00:00
-- url     : https://prove2.me/theorems/e6fb50f6-079c-4413-8e2c-102a148ad6a9
-- title:
--   The Lean 4 theorem `opNorm_le` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `opNorm_le` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvert.opNorm_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.IsShiftInvert.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    ‖R‖ ≤ γ⁻¹ := by sorry
