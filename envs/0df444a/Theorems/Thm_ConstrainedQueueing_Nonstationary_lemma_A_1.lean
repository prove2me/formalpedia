-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_lemma_A_1
-- name    : ConstrainedQueueing.Nonstationary.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:54.269313+00:00
-- url     : https://prove2.me/theorems/ceabe86b-8adf-45a5-8d59-8a4c205ce164
-- title:
--   Lemma A.1, p. 1945 — under C.1, co(S) is closed downward: c ∈ co(S), 0 ≤ x ≤ c ⇒ x ∈ co(S)
-- statement:
--   Let $S$ be a constraint set of activation sets of $N$ servers satisfying assumption C.1 (every subset of an activation set is an activation set), and let $\mathrm{co}(S)\subseteq\mathbb R^N$ be the convex hull of the activation vectors of $S$. Then $\mathrm{co}(S)$ is closed downward in the nonnegative orthant: for every $c\in\mathrm{co}(S)$ and every $x\in\mathbb R^N$,
--   $$0\le x\le c\ \ (\text{componentwise})\quad\Longrightarrow\quad x\in\mathrm{co}(S).$$
--
--   In the proof of Lemma 4.1 this is what turns a maximum flow, whose server components are bounded by a point of $\mathrm{co}(S)$, into a point of $\mathrm{co}(S)$ itself.
--
--   **Formalization Note.** The vectors are `Fin N → ℝ` with the componentwise order. C.1 is the only hypothesis; nonemptiness of $S$ follows from $c\in\mathrm{co}(S)$.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1945, Appendix, Lemma A.1

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

/-- Lemma A.1 (p. 1945): under C.1, if a vector `c` belongs to `co(S)`, then every vector `x`
with `0 ≤ x ≤ c` (componentwise) belongs to `co(S)` as well. -/
theorem lemma_A_1 {L N : ℕ} (net : Network L N) (hC1 : C1 net) :
    ∀ c ∈ coS net, ∀ x : Fin N → ℝ, 0 ≤ x → x ≤ c → x ∈ coS net := by sorry

end ConstrainedQueueing.Nonstationary
