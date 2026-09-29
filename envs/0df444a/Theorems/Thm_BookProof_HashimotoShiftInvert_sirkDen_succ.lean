-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_sirkDen_succ
-- name    : BookProof.HashimotoShiftInvert.sirkDen_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:22:57.746348+00:00
-- url     : https://prove2.me/theorems/3ef0411b-8328-43aa-a591-29ce890cee24
-- title:
--   The Lean 4 theorem `sirkDen_succ` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirkDen_succ` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.sirkDen_succ
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.sirkDen_succ (Xm : F →L[ℂ] F) (c : ℕ → ℂ) (k : ℕ) :
    sirkDen Xm c (k + 1) = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k := by sorry
