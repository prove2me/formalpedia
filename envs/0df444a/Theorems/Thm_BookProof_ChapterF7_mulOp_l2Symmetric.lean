-- Prove2me | Theorems.Thm_BookProof_ChapterF7_mulOp_l2Symmetric
-- name    : BookProof.ChapterF7.mulOp_l2Symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:42.71846+00:00
-- url     : https://prove2.me/theorems/1f068a83-64fe-49ae-8761-c7632e7b0397
-- title:
--   `BookProof.ChapterF7.mulOp_l2Symmetric` (v : ℝ → ℝ) (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) : IsL2Symmetric (mulOp v hv)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.mulOp_l2Symmetric` (v : ℝ → ℝ) (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) : IsL2Symmetric (mulOp v hv)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.mulOp_l2Symmetric`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.mulOp_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.mulOp_l2Symmetric (v : ℝ → ℝ)
    (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) :
    IsL2Symmetric (mulOp v hv) := by sorry
