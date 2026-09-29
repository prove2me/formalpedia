-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_sirkDen_commute
-- name    : BookProof.HashimotoShiftInvert.sirkDen_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:22:43.776056+00:00
-- url     : https://prove2.me/theorems/06f8edaf-0813-46c0-816b-0032438760e4
-- title:
--   The Lean 4 theorem `sirkDen_commute` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirkDen_commute` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.sirkDen_commute
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.sirkDen_commute {Xm T : F →L[ℂ] F} (c : ℕ → ℂ) (hT : T ∘L Xm = Xm ∘L T) (k : ℕ) :
    T ∘L sirkDen Xm c k = sirkDen Xm c k ∘L T := by sorry
