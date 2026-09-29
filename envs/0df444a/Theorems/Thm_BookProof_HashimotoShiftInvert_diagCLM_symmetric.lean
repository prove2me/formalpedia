-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_diagCLM_symmetric
-- name    : BookProof.HashimotoShiftInvert.diagCLM_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T10:26:12.389955+00:00
-- url     : https://prove2.me/theorems/8a5306bc-67b7-477c-b9a4-ed598ee8feb1
-- title:
--   The Lean 4 theorem `diagCLM_symmetric` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagCLM_symmetric` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.diagCLM_symmetric
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

theorem BookProof.HashimotoShiftInvert.diagCLM_symmetric {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x y : ℓ²(ℕ, ℂ)) :
    (inner ℂ (diagCLM hc x) y : ℂ) = inner ℂ x (diagCLM hc y) := by sorry
