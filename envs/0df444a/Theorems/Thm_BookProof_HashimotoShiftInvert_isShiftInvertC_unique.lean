-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_isShiftInvertC_unique
-- name    : BookProof.HashimotoShiftInvert.isShiftInvertC_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:24:11.109745+00:00
-- url     : https://prove2.me/theorems/4253ee06-0ea5-403f-84a8-9a9d76932406
-- title:
--   The Lean 4 theorem `isShiftInvertC_unique` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isShiftInvertC_unique` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.isShiftInvertC_unique
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.isShiftInvertC_unique {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A γ Y) : X = Y := by sorry
