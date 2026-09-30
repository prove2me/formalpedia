-- Prove2me | Theorems.Thm_AllocationIndices_index_gt_reward_of_index_increasing_once
-- name    : AllocationIndices.index_gt_reward_of_index_increasing_once
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:33:18.380985+00:00
-- url     : https://prove2.me/theorems/389f65d5-ad71-4fe4-952e-e0b1b46892c6
-- title:
--   Proposition 2.6: if ν(x(1)) > ν(x) almost surely, the supremum in (2.6) is attained at some τ > 1 and ν(x) > r(x)
-- statement:
--   **Proposition 2.6.** If $\Pr[\nu(x(1)) > \nu(x)] = 1$, the supremum in (2.6) is attained when $\tau > 1$, and $\nu(x) > r(x)$.
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, and a state $x$ such that, under $\mathbb{P}_x$, almost surely $\nu(B, x(1)) > \nu(B, x)$: there is a stopping time $\tau$ with $\tau \ge 2$ everywhere and $\nu_\tau(B, x) = \nu(B, x)$, and $r(x) < \nu(B, x)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.11.1 p. 45, Proposition 2.6

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_gt_reward_of_index_increasing_once {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x {ω | gittinsIndex P r a x < gittinsIndex P r a (ω 1)} = 1) :
    (∃ τ : (ℕ → S) → ℕ∞, IsPositiveStoppingTime τ ∧ (∀ ω, 2 ≤ τ ω) ∧
      stoppedRatio P r a τ x = gittinsIndex P r a x) ∧
    r x < gittinsIndex P r a x := by sorry

end AllocationIndices
