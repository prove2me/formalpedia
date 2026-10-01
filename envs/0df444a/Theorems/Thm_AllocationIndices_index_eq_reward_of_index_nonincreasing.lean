-- Prove2me | Theorems.Thm_AllocationIndices_index_eq_reward_of_index_nonincreasing
-- name    : AllocationIndices.index_eq_reward_of_index_nonincreasing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:32:39.595601+00:00
-- url     : https://prove2.me/theorems/82ebfe6b-347f-41f9-9805-4177bc97a5f7
-- title:
--   Proposition 2.5: if ν(x(1)) ≤ ν(x) almost surely, the supremum in (2.6) is attained at τ = 1 and ν(x) = r(x)
-- statement:
--   **Proposition 2.5.** If $\Pr[\nu(x(1)) \le \nu(x)] = 1$, the supremum in (2.6) is attained when $\tau = 1$, and $\nu(x) = r(x)$.
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, and a state $x$ such that, under $\mathbb{P}_x$, almost surely $\nu(B, x(1)) \le \nu(B, x)$: $\nu_1(B, x) = \nu(B, x)$ (the constant stopping time $1$ attains the supremum) and $\nu(B, x) = r(x)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.11.1 p. 45, Proposition 2.5

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_eq_reward_of_index_nonincreasing {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x {ω | gittinsIndex P r a (ω 1) ≤ gittinsIndex P r a x} = 1) :
    stoppedRatio P r a (fun _ ↦ 1) x = gittinsIndex P r a x ∧ gittinsIndex P r a x = r x := by sorry

end AllocationIndices
