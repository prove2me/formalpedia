-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_rkCompression_tendsto
-- name    : BookProof.HashimotoShiftInvert.rkCompression_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:16:21.761232+00:00
-- url     : https://prove2.me/theorems/c75bf969-4890-421c-ab18-45320302fe30
-- title:
--   The Lean 4 theorem `rkCompression_tendsto` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rkCompression_tendsto` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.rkCompression_tendsto
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HashimotoShiftInvert.rkCompression_tendsto (T : F →L[ℂ] F) (X : ℕ → F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ m : ℕ, rkSpan X v m : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun m : ℕ => rkCompression T X v m u) atTop (nhds (T u)) := by sorry
