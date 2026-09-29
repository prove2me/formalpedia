-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvertC_mem
-- name    : BookProof.HashimotoShiftInvert.IsShiftInvertC.mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:43:43.375716+00:00
-- url     : https://prove2.me/theorems/cbf46a1a-2f34-4428-aa39-8f69f6e7eb6f
-- title:
--   The Lean 4 theorem `mem` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.mem
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := by sorry
