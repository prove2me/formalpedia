-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_inner_nonneg
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvert.inner_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T20:21:15.568761+00:00
-- url     : https://prove2.me/theorems/9678274f-d683-4178-8717-2479f5a4719d
-- title:
--   The Lean 4 theorem `inner_nonneg` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_nonneg` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvert.inner_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.HashimotoShiftInvert.IsShiftInvert.inner_nonneg {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    0 ≤ (inner ℂ u (R u) : ℂ).re := by sorry
