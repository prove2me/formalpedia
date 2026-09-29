-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_diagCLM_isSelfAdjoint
-- name    : BookProof.HashimotoShiftInvert.diagCLM_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:31:48.472326+00:00
-- url     : https://prove2.me/theorems/aa11c668-8ef4-4301-9c47-c1f165236c95
-- title:
--   The Lean 4 theorem `diagCLM_isSelfAdjoint` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagCLM_isSelfAdjoint` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.diagCLM_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.diagCLM_isSelfAdjoint {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) :
    IsSelfAdjoint (diagCLM hc) := by sorry
