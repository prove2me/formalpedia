-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_flow_sub_stoneU_le
-- name    : BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:18:19.047246+00:00
-- url     : https://prove2.me/theorems/0965bcb8-b4e7-4c71-8cf9-36193e5b3967
-- title:
--   `BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le` {B : H →L[ℂ] H} (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le` {B : H →L[ℂ] H} (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) : ‖flow B t x - T.stoneU t x‖ ≤ K * t
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le {B : H →L[ℂ] H} (t : ℝ) (ht : 0 ≤ t) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖flow B t x - T.stoneU t x‖ ≤ K * t := by sorry
