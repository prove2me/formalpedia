-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_selfAdjointCriterion
-- name    : BookProof.HashimotoShiftInvert.invShiftOperator_selfAdjointCriterion
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:03:45.784132+00:00
-- url     : https://prove2.me/theorems/d27e7b1b-8968-4c79-97ad-2598f27cb511
-- title:
--   The Lean 4 theorem `invShiftOperator_selfAdjointCriterion` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `invShiftOperator_selfAdjointCriterion` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_selfAdjointCriterion
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterComplexShiftCore
open BookProof.QgOuterFockFL
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.invShiftOperator_selfAdjointCriterion (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by sorry
