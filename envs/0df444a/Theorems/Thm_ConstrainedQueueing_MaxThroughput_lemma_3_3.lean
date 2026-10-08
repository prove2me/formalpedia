-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_3_3
-- name    : ConstrainedQueueing.MaxThroughput.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:51.115144+00:00
-- url     : https://prove2.me/theorems/2a1b45f2-7ae8-4e57-9f02-dc6d2b237744
-- title:
--   Lemma 3.3, p. 1940 — if a ∉ C̄′ the system is unstable under every policy in H
-- statement:
--   Consider a constrained queueing network with service probabilities $0<m_i\le 1$. Let $\bar C'$ be the closure of $C'$.
--
--   **Lemma 3.3.** If $a\in(\bar C')^{c}$, then the system is unstable for any policy in $H$: for every activation rule $g$ and every arrival law with finite second moments and rates $a$, the queue-length chain under $g$ is not stable in the sense of Definition 3.1.
--
--   This is the converse half: no stationary policy stabilizes rates outside $\bar C'$.
--
--   **Formalization Note.** Neither C.1, C.2 nor $\emptyset\in S$ is assumed; the statement concerns every activation rule.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1940, Lemma 3.3

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- Lemma 3.3 (p. 1940): if `a ∉ C̄′`, the system is unstable under every policy in `H`. -/
theorem lemma_3_3 {L N J : ℕ} (net : Network L N J) (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) :
    ∀ g, IsActivationRule net g → ∀ α : ArrivalLaw net, Admissible α →
      meanRate α ∉ closure (Cprime net) → ¬ IsStable (transProb net g α) := by sorry

end ConstrainedQueueing.MaxThroughput
