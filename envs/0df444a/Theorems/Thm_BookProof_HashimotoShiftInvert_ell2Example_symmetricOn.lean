-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_ell2Example_symmetricOn
-- name    : BookProof.HashimotoShiftInvert.ell2Example_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:25:15.086339+00:00
-- url     : https://prove2.me/theorems/3b1cbe5d-f145-41e5-80a6-49e99e1ae252
-- title:
--   The Lean 4 theorem `ell2Example_symmetricOn` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ell2Example_symmetricOn` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.ell2Example_symmetricOn
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








open scoped ENNReal InnerProductSpace lp

theorem BookProof.HashimotoShiftInvert.ell2Example_symmetricOn :
    SymmetricOn (LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)))
      ell2UnboundedExample := by sorry
