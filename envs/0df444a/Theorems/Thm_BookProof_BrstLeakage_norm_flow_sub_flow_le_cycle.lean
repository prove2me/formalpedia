-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_flow_sub_flow_le_cycle
-- name    : BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:30:34.964979+00:00
-- url     : https://prove2.me/theorems/cbde04c7-33c6-49ff-8cf7-35920f19e19e
-- title:
--   `BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle` {H B : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B) (tau : ℝ) (htau : 0 ≤ tau) (w : E) : ‖flow H tau w - flow B tau
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle` {H B : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B) (tau : ℝ) (htau : 0 ≤ tau) (w : E) : ‖flow H tau w - flow B tau w‖ ≤ (‖H - B‖ * tau) * ‖w‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle {H B : E →L[ℂ] E} (hH : IsSelfAdjoint H)
    (hB : IsSelfAdjoint B) (tau : ℝ) (htau : 0 ≤ tau) (w : E) :
    ‖flow H tau w - flow B tau w‖ ≤ (‖H - B‖ * tau) * ‖w‖ := by sorry
