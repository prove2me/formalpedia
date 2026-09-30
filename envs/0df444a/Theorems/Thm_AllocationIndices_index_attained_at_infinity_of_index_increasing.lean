-- Prove2me | Theorems.Thm_AllocationIndices_index_attained_at_infinity_of_index_increasing
-- name    : AllocationIndices.index_attained_at_infinity_of_index_increasing
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:34:33.854986+00:00
-- url     : https://prove2.me/theorems/cf731a59-1378-40f0-9028-b152d379fc05
-- title:
--   Proposition 2.8: if ν(x(t)) > ν(x) for all t ≥ 1 almost surely, the supremum in (2.6) is attained at τ = ∞ and ν(x) > r(x)
-- statement:
--   **Proposition 2.8.** If $\Pr[\nu(x(t)) > \nu(x),\ t = 1, 2, \dots] = 1$, the supremum in (2.6) is attained when $\tau = \infty$, and $\nu(x) > r(x)$.
--
--   Formally: for a bandit process on a countable state space with bounded reward and $a \in (0,1)$, and a state $x$ such that, under $\mathbb{P}_x$, almost surely $\nu(B, x(t)) > \nu(B, x)$ for every $t \ge 1$: the never-stopping time $\tau \equiv \infty$ attains the supremum, $\nu_\infty(B, x) = \mathbb{E}_x[\sum_{t \ge 0} a^t r(x(t))] / \mathbb{E}_x[\sum_{t \ge 0} a^t] = \nu(B, x)$, and $r(x) < \nu(B, x)$. This includes the case when $\nu(x(t))$ is almost surely increasing.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.11.1 p. 45, Proposition 2.8

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem index_attained_at_infinity_of_index_increasing {S : Type*} [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x
      {ω | ∀ t : ℕ, 1 ≤ t → gittinsIndex P r a x < gittinsIndex P r a (ω t)} = 1) :
    stoppedRatio P r a (fun _ ↦ ⊤) x = gittinsIndex P r a x ∧ r x < gittinsIndex P r a x := by sorry

end AllocationIndices
