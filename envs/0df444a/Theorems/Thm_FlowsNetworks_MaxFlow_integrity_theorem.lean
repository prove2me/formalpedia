-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_integrity_theorem
-- name    : FlowsNetworks.MaxFlow.integrity_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:12.852753+00:00
-- url     : https://prove2.me/theorems/31fd603b-8900-4c7d-bfc8-e0b554906f1d
-- title:
--   Chapter I, Theorem 8.1 — integrity theorem: integral capacities admit an integral maximal flow
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$, and let $s \neq t$. If the capacity function is integral valued, $c(x, y) \in \mathbb Z$ for every arc, then there is a maximal flow $f$ from $s$ to $t$ that is also integral valued:
--   $$\exists f \text{ maximal flow from } s \text{ to } t \text{ with } f(x, y) \in \mathbb Z \text{ for all } (x, y) \in \mathcal A.$$
--
--   The integrity theorem is what makes network flows a tool for combinatorics: every application of the max flow min cut theorem to matchings, disjoint paths or systems of representatives in the later chapters rests on it.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). Capacities and flows are real valued; integrality is the explicit statement that each value on an arc is (the image of) an integer.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 34, Theorem 8.1

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 8.1 (integrity theorem, p. 34): if the
capacity function `c` is integral valued, there exists a maximal flow `f` that is also integral
valued. -/
theorem integrity_theorem {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hc : ∀ p ∈ G.arcs, ∃ n : ℤ, G.cap p.1 p.2 = n) :
    ∃ f : N → N → ℝ, IsMaxFlow G s t f ∧ ∀ p ∈ G.arcs, ∃ n : ℤ, f p.1 p.2 = n := by sorry

end FlowsNetworks.MaxFlow
