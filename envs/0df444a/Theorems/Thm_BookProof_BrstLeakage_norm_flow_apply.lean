-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_flow_apply
-- name    : BookProof.BrstLeakage.norm_flow_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:30:08.103348+00:00
-- url     : https://prove2.me/theorems/e8eb3025-0f47-4581-8eeb-0a19918ea4ea
-- title:
--   `BookProof.BrstLeakage.norm_flow_apply` {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (x : E) : ‖flow A t x‖ = ‖x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_flow_apply` {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (x : E) : ‖flow A t x‖ = ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_flow_apply`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_flow_apply
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_flow_apply {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (x : E) :
    ‖flow A t x‖ = ‖x‖ := by sorry
