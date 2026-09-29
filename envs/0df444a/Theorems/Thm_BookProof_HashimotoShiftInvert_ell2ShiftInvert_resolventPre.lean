-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_ell2ShiftInvert_resolventPre
-- name    : BookProof.HashimotoShiftInvert.ell2ShiftInvert_resolventPre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:25:59.91327+00:00
-- url     : https://prove2.me/theorems/9030f592-7f2a-4a1c-b2ad-caed6ec4fc78
-- title:
--   The Lean 4 theorem `ell2ShiftInvert_resolventPre` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ell2ShiftInvert_resolventPre` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.ell2ShiftInvert_resolventPre
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

theorem BookProof.HashimotoShiftInvert.ell2ShiftInvert_resolventPre {γ : ℂ} (hγ : γ.im ≠ 0) (u : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert (ell2ResolventPre hγ u) = ell2Resolvent hγ u := by sorry
