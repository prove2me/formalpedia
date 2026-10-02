-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_isShiftInvert_unique
-- name    : BookProof.HashimotoShiftInvert.isShiftInvert_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T09:29:28.850997+00:00
-- url     : https://prove2.me/theorems/656cf6a0-58e9-4cb3-b6ab-f0b1a205e5fa
-- title:
--   The Lean 4 theorem `isShiftInvert_unique` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isShiftInvert_unique` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.isShiftInvert_unique
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.isShiftInvert_unique {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R S : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hS : IsShiftInvert A γ S) : R = S := by sorry
