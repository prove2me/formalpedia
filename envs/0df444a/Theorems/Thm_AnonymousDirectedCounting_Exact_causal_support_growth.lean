-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_causal_support_growth
-- name    : AnonymousDirectedCounting.Exact.causal_support_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:48.355202+00:00
-- url     : https://prove2.me/theorems/c9a29485-6c13-457f-8ad0-861fa23c316a
-- title:
--   Lemma 5 — causal support growth
-- statement:
--   Let $G$ be an admissible network of $n$ agents, let $x$ be an agent and let $0\le r\le t$. Write $\mathcal L_r$ for level $r$ of the round-$t$ vista of $x$. Then
--   $$
--   \left|\bigcup_{v\in\mathcal L_r}A(v)\right|\ge\min\{n,t-r+1\}.
--   $$
--   This is the quantitative expansion behind the delay property H4 and the all-leader test.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 5, printed p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 5, printed p. 19 (PDF p. 21). The fibers of `L_r` together contain at least
`min {n, t - r + 1}` agents. -/
theorem causal_support_growth {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (t : ℕ) (x : Fin n) (r : ℕ) (hr : r ≤ t) :
    min n (t - r + 1) ≤ (unionFibers G r (agentLevel G t x r)).card := by sorry

end AnonymousDirectedCounting.Exact
