-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_dom_eq_range
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T20:12:55.856192+00:00
-- url     : https://prove2.me/theorems/ca08d33b-604a-4a51-ac52-3599bae072a4
-- title:
--   The Lean 4 theorem `dom_eq_range` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dom_eq_range` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Dom = LinearMap.range (R : F →ₗ[ℂ] F) := by sorry
