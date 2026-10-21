-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_family_index_eq_max_index
-- name    : AllocationIndices.Freezing.family_index_eq_max_index
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:29.707093+00:00
-- url     : https://prove2.me/theorems/1bc68a3e-e591-4c5b-a4b4-c12b608195a1
-- title:
--   Lemma 4.6(i) — the index of a simple family is the largest index of its members: $\nu(F) = \max_j \nu(B_j)$
-- statement:
--   Let $F$ be a simple family of $k \ge 1$ alternative bandit processes $B_1, \dots, B_k$ on a common countable state space $S$, with a common transition kernel $P$, bounded reward $r$ and discount factor $0 < a < 1$; at each decision time a policy continues exactly one bandit, and only that bandit changes state. Let $x = (x_1, \dots, x_k)$ be the initial state-vector. The index of the family is
--   $$\nu(F, x) = \sup_{g, \tau} \frac{R_{g\tau}(F, x)}{W_{g\tau}(F, x)},$$
--   the supremum over all (history-dependent, possibly randomized) policies $g$ and positive stopping times $\tau$ of the family, where $R_{g\tau}$ and $W_{g\tau}$ are the expected discounted reward and the expected discounted time accrued before $\tau$ under $g$. Then
--   $$\nu(F, x) = \max_{1 \le j \le k} \nu(B_j, x_j),$$
--   where $\nu(B_j, x_j)$ is the Gittins index of $B_j$ in its initial state.
--
--   Thus no way of interleaving the bandits of the family, and no stopping time, earns a higher reward rate than the best single bandit; this is part (i) of Lemma 4.6, and the step of the proof of the index theorem by freezing rules in which the remaining bandits, taken together, are shown to have index at most that of the bandit of greatest index.
--
--   **Formalization Note** Different bandit processes are encoded, as in the published `MarkovBanditPolicy`, by $k$ copies of one kernel on a common state space (disjoint unions give the general case, §2.9). Time is discrete; $W_{g\tau}(F, x) = \sum_t a^t P_g(\tau > t) \ge 1$. The book's $n$ bandits are `k` with `0 < k`. A stopping time of the family is a "still running" flag on histories with $\tau > 0$ that, once false, stays false; on a countable state space all such flags are past-measurable. Parts (ii) and (iii) of Lemma 4.6 are not stated.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5.1 p. 94, Lemma 4.6(i); Eq. (4.5) p. 90

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem family_index_eq_max_index {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ} (hk : 0 < k)
    (x : Fin k → T) :
    familyIndex P r a x = ⨆ j : Fin k, gittinsIndex P r a (x j) := by sorry

end AllocationIndices.Freezing
