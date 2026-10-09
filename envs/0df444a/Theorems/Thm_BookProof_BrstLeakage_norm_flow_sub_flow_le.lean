-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_flow_sub_flow_le
-- name    : BookProof.BrstLeakage.norm_flow_sub_flow_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:13:03.577991+00:00
-- url     : https://prove2.me/theorems/9e42c22f-e876-41d0-bca4-f68b38966fe4
-- title:
--   `BookProof.BrstLeakage.norm_flow_sub_flow_le` {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (t : ℝ) (ht : 0 ≤ t) : ‖flow A t - flow B t‖ ≤ ‖A - B‖ * t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_flow_sub_flow_le` {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (t : ℝ) (ht : 0 ≤ t) : ‖flow A t - flow B t‖ ≤ ‖A - B‖ * t
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_flow_sub_flow_le`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_flow_sub_flow_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_flow_sub_flow_le {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) (t : ℝ) (ht : 0 ≤ t) :
    ‖flow A t - flow B t‖ ≤ ‖A - B‖ * t := by sorry
