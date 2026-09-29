-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_rkProj_tendsto
-- name    : BookProof.HashimotoShiftInvert.rkProj_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:24:23.648205+00:00
-- url     : https://prove2.me/theorems/94a293b2-9c01-4068-946d-b9c5c82e5b00
-- title:
--   The Lean 4 theorem `rkProj_tendsto` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rkProj_tendsto` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.rkProj_tendsto
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HashimotoShiftInvert.rkProj_tendsto (X : ℕ → F →L[ℂ] F) (v : F)
    (hdense : Dense ((⨆ m : ℕ, rkSpan X v m : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun m : ℕ => (rkSpan X v m).starProjection u) atTop (nhds u) := by sorry
