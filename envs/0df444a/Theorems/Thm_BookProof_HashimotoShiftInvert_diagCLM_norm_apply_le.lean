-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_diagCLM_norm_apply_le
-- name    : BookProof.HashimotoShiftInvert.diagCLM_norm_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T10:25:58.733463+00:00
-- url     : https://prove2.me/theorems/ff86b661-97b9-4fcb-8cb4-a80c7bec22f1
-- title:
--   The Lean 4 theorem `diagCLM_norm_apply_le` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagCLM_norm_apply_le` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.diagCLM_norm_apply_le
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

theorem BookProof.HashimotoShiftInvert.diagCLM_norm_apply_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    ‖diagCLM hc x‖ ≤ ‖x‖ := by sorry
