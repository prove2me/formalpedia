-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_ell2Resolvent_isShiftInvertC
-- name    : BookProof.HashimotoShiftInvert.ell2Resolvent_isShiftInvertC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:16:01.574667+00:00
-- url     : https://prove2.me/theorems/9289fc1b-a22b-4b87-b66d-1b1e4b3256f3
-- title:
--   The Lean 4 theorem `ell2Resolvent_isShiftInvertC` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ell2Resolvent_isShiftInvertC` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.ell2Resolvent_isShiftInvertC
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]








open scoped InnerProductSpace ENNReal

theorem BookProof.HashimotoShiftInvert.ell2Resolvent_isShiftInvertC {γ : ℂ} (hγ : γ.im ≠ 0) :
    IsShiftInvertC ell2UnboundedExample γ (ell2Resolvent hγ) := by sorry
