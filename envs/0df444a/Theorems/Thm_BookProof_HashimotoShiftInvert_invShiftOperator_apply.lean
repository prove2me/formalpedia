-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_apply
-- name    : BookProof.HashimotoShiftInvert.invShiftOperator_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T14:08:32.673775+00:00
-- url     : https://prove2.me/theorems/1c765355-3681-400e-a281-e8e4b5da0ccd
-- title:
--   The Lean 4 theorem `invShiftOperator_apply` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.HashimotoShiftInvert.invShiftOperator_apply` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHashimotoShiftInvert.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.invShiftOperator_apply (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := by sorry
