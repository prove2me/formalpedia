-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_leakage_le
-- name    : BookProof.BrstUnboundedLeakage.leakage_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:18:30.351781+00:00
-- url     : https://prove2.me/theorems/4434a01a-38e1-4aa2-84fd-773dcdace3da
-- title:
--   `BookProof.BrstUnboundedLeakage.leakage_le` {B Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.leakage_le` {B Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) : ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.leakage_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.leakage_le
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

theorem BookProof.BrstUnboundedLeakage.leakage_le {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by sorry
