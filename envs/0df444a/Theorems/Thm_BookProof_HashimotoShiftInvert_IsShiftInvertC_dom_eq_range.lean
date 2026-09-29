-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_dom_eq_range
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.dom_eq_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:22:43.85131+00:00
-- url     : https://prove2.me/theorems/c6cdf38e-0c1c-49bf-824f-9f40e2e3030e
-- title:
--   The Lean 4 theorem `dom_eq_range` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dom_eq_range` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.dom_eq_range
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Dom = LinearMap.range (X : F →ₗ[ℂ] F) := by sorry
