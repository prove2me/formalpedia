-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_isPositiveSelfAdjointExtension
-- name    : BookProof.HashimotoShiftInvert.invShiftOperator_isPositiveSelfAdjointExtension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:24:08.680827+00:00
-- url     : https://prove2.me/theorems/2886b99c-a6e0-42ea-8bc9-5020dd2e5d40
-- title:
--   The Lean 4 theorem `invShiftOperator_isPositiveSelfAdjointExtension` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `invShiftOperator_isPositiveSelfAdjointExtension` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.invShiftOperator_isPositiveSelfAdjointExtension (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ) (hR : IsSelfAdjoint R)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) := by sorry
