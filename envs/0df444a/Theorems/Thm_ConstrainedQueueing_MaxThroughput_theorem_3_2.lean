-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_theorem_3_2
-- name    : ConstrainedQueueing.MaxThroughput.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:47.073141+00:00
-- url     : https://prove2.me/theorems/729f4dc8-fb43-4374-84e5-62d25692d6ea
-- title:
--   Theorem 3.2, p. 1940 — C′ ⊂ C ⊂ C̄′, and C′ ⊂ C_π₀ ⊂ C ⊂ C̄_π₀ for every π₀ rule
-- statement:
--   Consider a constrained queueing network with $L$ nodes, $N$ servers and $J$ classes, satisfying C.1 (the constraint set $S$ is closed under subsets) and C.2 (every non-destination node can forward each class to one of its destinations), with $\emptyset\in S$, every single server forming an activation set, and service probabilities $0<m_i\le 1$. Let $C'$ be the set of rate vectors of p. 1940, $C=\bigcup_{\pi\in H}C_\pi$ the stability region of the system, and $C_{\pi_0}$ the stability region of policy $\pi_0$.
--
--   **Theorem 3.2.** The set $C'$ characterizes the system stability region in the sense
--   $$C'\subset C\subset\bar C',$$
--   and for the stability region of policy $\pi_0$ we have
--   $$C'\subset C_{\pi_0}\subset C\subset\bar C_{\pi_0}.$$
--   The second chain holds for every activation rule of $\pi_0$, whatever its tie-breaking; inclusions are not strict.
--
--   So the max-weight (back-pressure) policy $\pi_0$ stabilizes the network whenever any stationary policy does, up to the boundary of $C'$: it is throughput-optimal.
--
--   **Formalization Note.** $C_\pi$ is the set of nonnegative rate vectors for which the chain is stable for every arrival law with finite second moments and those rates; $C$ is its union over activation rules. C.2 is used in its topological form, and $\{i\}\in S$ for every server $i$ is the assumption used implicitly at (A.24) in the proof of Lemma 3.2. Indices are $0$-based.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1940, Theorem 3.2

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- Theorem 3.2 (p. 1940): `C′ ⊂ C ⊂ C̄′`, and `C′ ⊂ C_{π₀} ⊂ C ⊂ C̄_{π₀}` for every activation
rule of policy `π₀` (inclusions are not strict). -/
theorem theorem_3_2 {L N J : ℕ} (net : Network L N J) (hC1 : C1 net)
    (hempty : (∅ : Finset (Fin N)) ∈ net.S) (hsingle : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ net.S)
    (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) (hC2 : C2 net) :
    Cprime net ⊆ sysStabRegion net ∧ sysStabRegion net ⊆ closure (Cprime net) ∧
      ∀ g, IsPi0Rule net g →
        Cprime net ⊆ stabRegion net g ∧ stabRegion net g ⊆ sysStabRegion net ∧
          sysStabRegion net ⊆ closure (stabRegion net g) := by sorry

end ConstrainedQueueing.MaxThroughput
