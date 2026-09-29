-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_norm_single_one
-- name    : BookProof.HashimotoShiftInvert.norm_single_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T10:26:20.585413+00:00
-- url     : https://prove2.me/theorems/543ae566-c674-406e-aab6-ce89fd3f1bea
-- title:
--   The Lean 4 theorem `norm_single_one` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_single_one` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.norm_single_one
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.HashimotoShiftInvert
open scoped lp



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open scoped lp
open BookProof.HermiteGalerkin
open scoped lp
open Filter Topology
open scoped lp

theorem BookProof.HashimotoShiftInvert.norm_single_one (k : ℕ) : ‖(lp.single 2 k (1 : ℂ) : ℓ²(ℕ, ℂ))‖ = 1 := by sorry
