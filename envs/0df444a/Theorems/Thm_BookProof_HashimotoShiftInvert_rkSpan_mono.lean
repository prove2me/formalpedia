-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_rkSpan_mono
-- name    : BookProof.HashimotoShiftInvert.rkSpan_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:22:49.020646+00:00
-- url     : https://prove2.me/theorems/fcf346e7-f36f-4953-bcd7-7aee6a6cf1c4
-- title:
--   The Lean 4 theorem `rkSpan_mono` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rkSpan_mono` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.rkSpan_mono
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

theorem BookProof.HashimotoShiftInvert.rkSpan_mono (X : ℕ → F →L[ℂ] F) (v : F) {m n : ℕ} (hmn : m ≤ n) :
    rkSpan X v m ≤ rkSpan X v n := by sorry
