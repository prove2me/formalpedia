-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_lemma_3_1
-- name    : ConstrainedQueueing.MaxThroughput.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:36.584218+00:00
-- url     : https://prove2.me/theorems/c2dacc87-ff88-44ae-b220-cd5f97b3708d
-- title:
--   Lemma 3.1, p. 1940 — the closure of C′ is {a : ∃ f ∈ F_a, c ∈ co(S), M⁻¹f̂ ≤ c}
-- statement:
--   Consider a constrained queueing network with service probabilities $m_i>0$, and let $M$ be the diagonal matrix with entries $m_1,\dots,m_N$. Let $F_a$ be the set of $a$-admissible multicommodity flows, $\hat f=\sum_j f^j$ the total flow, and $C'$ the set of arrival-rate vectors defined on p. 1940 (see the Model definition).
--
--   **Lemma 3.1.** The closure $\bar C'$ of $C'$ is
--   $$\bar C'=\{a\ge 0:\ \text{there exist } f\in F_a \text{ and } c\in\mathrm{co}(S) \text{ with } M^{-1}\hat f\le c\}.$$
--
--   Thus the strict inequalities in the definition of $C'$ become non-strict on the boundary. The lemma identifies the outer bound $\bar C'$ of the stability region in a form that no stationary policy can exceed.
--
--   **Formalization Note.** Rate vectors are indexed by the queues $(l,j)$ with $l\notin V_j$; the condition $a\ge 0$ is part of both sides (the paper's rate vectors are nonnegative). $M^{-1}\hat f\le c$ is written componentwise as $\hat f_i/m_i\le c_i$.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1940, Lemma 3.1

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- Lemma 3.1 (p. 1940): `C̄′ = {a ≥ 0 : ∃ f ∈ F_a, ∃ c ∈ co(S), M⁻¹ f̂ ≤ c}`. -/
theorem lemma_3_1 {L N J : ℕ} (net : Network L N J) (hm : ∀ i, 0 < net.m i) :
    closure (Cprime net) =
      {a | (∀ p, 0 ≤ a p) ∧ ∃ f, IsAdmissibleFlow net a f ∧
        ∃ c ∈ coS net, ∀ i, fhat f i / net.m i ≤ c i} := by sorry

end ConstrainedQueueing.MaxThroughput
