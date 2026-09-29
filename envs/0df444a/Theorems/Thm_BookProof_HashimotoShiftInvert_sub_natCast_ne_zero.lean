-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_sub_natCast_ne_zero
-- name    : BookProof.HashimotoShiftInvert.sub_natCast_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:23:09.828514+00:00
-- url     : https://prove2.me/theorems/19bd467c-6d54-4bdc-9b2a-1b667900485e
-- title:
--   The Lean 4 theorem `sub_natCast_ne_zero` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sub_natCast_ne_zero` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.sub_natCast_ne_zero
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

theorem BookProof.HashimotoShiftInvert.sub_natCast_ne_zero {γ : ℂ} (hγ : γ.im ≠ 0) (n : ℕ) : γ - (n : ℂ) ≠ 0 := by sorry
