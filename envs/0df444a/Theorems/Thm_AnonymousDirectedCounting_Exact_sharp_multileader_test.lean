-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_sharp_multileader_test
-- name    : AnonymousDirectedCounting.Exact.sharp_multileader_test
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:35.080568+00:00
-- url     : https://prove2.me/theorems/1029e9b1-ab41-4a2e-b6dd-9032901505a6
-- title:
--   Lemma 7 — sharp multi-leader test
-- statement:
--   Let $G$ be an admissible network with $\ell\ge2$ leaders and $n$ agents, and let $x$ be an agent. For every candidate $\ell<m<n$, the test with final level $\mathcal L_{m-1}$ rejects $m$ on the round-$(2m-2)$ vista of $x$. If $n>\ell$, the same test accepts $n$ on the round-$(2n-2)$ vista of $x$. This gives the improvement by one round over the core algorithm.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - encoding: the test performed by an agent at its round → Accepts evaluated on the agent's all-active node at that round; reason: this is the source's vista; that no agent has halted earlier is the content of the surrounding argument and of the goal, whose statement is about the actual execution
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 7, printed p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 7, printed p. 19 (PDF p. 21). For `ℓ ≥ 2`, the test of that page (round `2m - 2`, final
level `L_{m-1}`) rejects every candidate `ℓ < m < n` at its round, and accepts `m = n > ℓ` at round
`2n - 2`. -/
theorem sharp_multileader_test {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (hℓ : 2 ≤ G.leaders.card) (x : Fin n) :
    (∀ m : ℕ, G.leaders.card < m → m < n →
      ¬ Accepts G.leaders.card (m - 1) m (history G (2 * m - 2) x)) ∧
    (G.leaders.card < n →
      Accepts G.leaders.card (n - 1) n (history G (2 * n - 2) x)) := by sorry

end AnonymousDirectedCounting.Exact
