-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_isShiftInvert_invShiftOperator
-- name    : BookProof.HashimotoShiftInvert.isShiftInvert_invShiftOperator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:41.739415+00:00
-- url     : https://prove2.me/theorems/0a19d144-4281-48f0-9b77-9a15fcedbbb3
-- title:
--   The Lean 4 theorem `isShiftInvert_invShiftOperator` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isShiftInvert_invShiftOperator` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.isShiftInvert_invShiftOperator
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HashimotoShiftInvert.isShiftInvert_invShiftOperator (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ) :
    IsShiftInvert (invShiftOperator R hinj γ) γ R := by sorry
