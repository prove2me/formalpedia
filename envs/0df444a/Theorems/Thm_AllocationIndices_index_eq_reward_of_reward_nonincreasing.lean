-- Prove2me | Theorems.Thm_AllocationIndices_index_eq_reward_of_reward_nonincreasing
-- name    : AllocationIndices.index_eq_reward_of_reward_nonincreasing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:33:51.017984+00:00
-- url     : https://prove2.me/theorems/60fe9e67-a4dc-4ad0-994c-0a917e048b81
-- title:
--   Proposition 2.7: if r(x(t)) ≤ r(x) for all t ≥ 1 almost surely, the supremum in (2.6) is attained at τ = 1 and ν(x) = r(x)
-- statement:
--   **Proposition 2.7.** If $\Pr[r(x(t)) \le r(x),\ t = 1, 2, \dots] = 1$, the supremum in (2.6) is attained when $\tau = 1$, and $\nu(x) = r(x)$.
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, and a state $x$ such that, under $\mathbb{P}_x$, almost surely $r(x(t)) \le r(x)$ for every $t \ge 1$: $\nu_1(B, x) = \nu(B, x)$ and $\nu(B, x) = r(x)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.11.1 p. 45, Proposition 2.7 with the preceding computation

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_eq_reward_of_reward_nonincreasing {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x {ω | ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x} = 1) :
    stoppedRatio P r a (fun _ ↦ 1) x = gittinsIndex P r a x ∧ gittinsIndex P r a x = r x := by sorry

end AllocationIndices
