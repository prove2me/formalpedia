-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_symmetricOn
-- name    : BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T14:08:51.486152+00:00
-- url     : https://prove2.me/theorems/82c9b3e5-29cf-4831-b6dc-1cf0bdd6cb55
-- title:
--   The Lean 4 theorem `invShiftOperator_symmetricOn` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHashimotoShiftInvert.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn
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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (hR : IsSelfAdjoint R) :
    SymmetricOn (LinearMap.range (R : F →ₗ[ℂ] F)) (invShiftOperator R hinj γ) := by sorry
