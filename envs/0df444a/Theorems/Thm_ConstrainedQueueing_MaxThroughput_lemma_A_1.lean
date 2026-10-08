-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_A_1
-- name    : ConstrainedQueueing.MaxThroughput.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:26.150979+00:00
-- url     : https://prove2.me/theorems/c295069d-338e-434b-a1e6-4e8f4d7b6fd9
-- title:
--   Lemma A.1, p. 1945 — co(S) is closed under 0 ≤ a ≤ c
-- statement:
--   Let $S$ be the constraint set of a constrained queueing network with $N$ servers, viewed as a family of subsets of $\{1,\dots,N\}$, and let $\mathrm{co}(S)\subset\mathbb R^N$ be the convex hull of the indicator vectors of its elements. Assume **C.1**: every subset of an activation set is an activation set.
--
--   **Lemma A.1.** If $c\in\mathrm{co}(S)$ and $a\in\mathbb R^N$ satisfies
--   $$0\le a\le c\quad\text{(componentwise)},$$
--   then $a\in\mathrm{co}(S)$.
--
--   The lemma says that the capacity region $\mathrm{co}(S)$ is downward closed in the nonnegative orthant; it is used to scale a feasible service vector in the drift argument for policy $\pi_0$.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1945, Appendix, Lemma A.1

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- Lemma A.1 (p. 1945): under C.1, `co(S)` is closed under `0 ≤ a ≤ c`. -/
theorem lemma_A_1 {L N J : ℕ} (net : Network L N J) (hC1 : C1 net) :
    ∀ c ∈ coS net, ∀ a : Fin N → ℝ, 0 ≤ a → a ≤ c → a ∈ coS net := by sorry

end ConstrainedQueueing.MaxThroughput
