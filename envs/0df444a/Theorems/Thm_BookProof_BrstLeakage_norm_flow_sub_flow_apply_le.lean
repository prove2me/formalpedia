-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_flow_sub_flow_apply_le
-- name    : BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:31.803988+00:00
-- url     : https://prove2.me/theorems/b82edce1-2bd2-47ee-ae83-2da148528448
-- title:
--   `BookProof.BrstLeakage.norm_flow_sub_flow_apply_le` {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(A - B) (flow B s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_flow_sub_flow_apply_le` {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(A - B) (flow B s x)‖ ≤ K) : ‖flow B t x - flow A t x‖ ≤ K * t
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_flow_sub_flow_apply_le`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_flow_sub_flow_apply_le {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(A - B) (flow B s x)‖ ≤ K) :
    ‖flow B t x - flow A t x‖ ≤ K * t := by sorry
