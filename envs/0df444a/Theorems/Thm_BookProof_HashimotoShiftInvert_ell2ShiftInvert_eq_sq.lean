-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_ell2ShiftInvert_eq_sq
-- name    : BookProof.HashimotoShiftInvert.ell2ShiftInvert_eq_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:07:57.646448+00:00
-- url     : https://prove2.me/theorems/998fe3fa-5451-4978-b953-0dcf2e7fe335
-- title:
--   The Lean 4 theorem `ell2ShiftInvert_eq_sq` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ell2ShiftInvert_eq_sq` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.ell2ShiftInvert_eq_sq
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_sqrtInvCoeff_abs_le_one
open BookProof.HashimotoShiftInvert
open scoped lp



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open scoped lp
open BookProof.HermiteGalerkin
open scoped lp
open Filter Topology
open scoped lp

theorem BookProof.HashimotoShiftInvert.ell2ShiftInvert_eq_sq (x : ℓ²(ℕ, ℂ)) :
    ell2ShiftInvert x = diagCLM sqrtInvCoeff_abs_le_one (diagCLM sqrtInvCoeff_abs_le_one x) := by sorry
