-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_3_2
-- name    : ConstrainedQueueing.MaxThroughput.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:37.29815+00:00
-- url     : https://prove2.me/theorems/976f74bb-93ca-4bd8-a805-9a5ebca6e91d
-- title:
--   Lemma 3.2, p. 1940 — under π₀ the system is stable for every a ∈ C′: C′ ⊂ C_π₀
-- statement:
--   Consider a constrained queueing network satisfying C.1 and C.2, with $\emptyset\in S$, every single server forming an activation set, and service probabilities $0<m_i\le1$. Let $g$ be any activation rule of policy $\pi_0$ (with arbitrary tie-breaking).
--
--   **Lemma 3.2.** Under policy $\pi_0$ the system is stable for every $a\in C'$:
--   $$C'\subset C_{\pi_0}.$$
--   That is, for every rate vector $a\in C'$ and every arrival law with finite second moments and rates $a$, the queue-length chain under $g$ is stable in the sense of Definition 3.1.
--
--   This is the achievability half of the throughput optimality of $\pi_0$.
--
--   **Formalization Note.** $C_{\pi_0}$ is the set of nonnegative rate vectors for which the chain is stable for every admissible arrival law with those rates. C.2 is used in its topological form (every non-destination node can forward class $j$ to $V_j$), and the singleton hypothesis $\{i\}\in S$ is the assumption used implicitly at (A.24) of the proof.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1940, Lemma 3.2

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- Lemma 3.2 (p. 1940): under policy `π₀` the system is stable for every `a ∈ C′`:
`C′ ⊂ C_{π₀}`. -/
theorem lemma_3_2 {L N J : ℕ} (net : Network L N J) (hC1 : C1 net)
    (hempty : (∅ : Finset (Fin N)) ∈ net.S) (hsingle : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ net.S)
    (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) (hC2 : C2 net)
    (g : (QIdx net → ℕ) → MultiAct N J) (hg : IsPi0Rule net g) :
    Cprime net ⊆ stabRegion net g := by sorry

end ConstrainedQueueing.MaxThroughput
