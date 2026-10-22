-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_minimal_cut_iff_saturated
-- name    : FlowsNetworks.MaxFlow.minimal_cut_iff_saturated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:02.038167+00:00
-- url     : https://prove2.me/theorems/9ba33547-e3d6-48bd-822d-42238528792e
-- title:
--   Chapter I, Corollary 5.3 — a cut is minimal iff every maximal flow saturates it forward and leaves it flowless backward
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$, let $s \neq t$, and let $X \subseteq N$ with $s \in X$, $t \notin X$. Then the cut $(X, \bar X)$ is minimal if and only if, for every maximal flow $f$ from $s$ to $t$,
--   $$f(x, y) = c(x, y) \text{ for all } (x, y) \in (X, \bar X) \quad\text{and}\quad f(x, y) = 0 \text{ for all } (x, y) \in (\bar X, X),$$
--   that is, $f$ **saturates** every arc of $(X, \bar X)$ and every arc of $(\bar X, X)$ is **flowless**.
--
--   This characterizes minimal cuts in terms of a single maximal flow's behaviour on the cut, and is the tool for Corollary 5.4 and Theorem 5.5.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). The cut is given by its node set $X$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 23, Corollary 5.3

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Corollary 5.3 (p. 23): a cut `(X, X̄)` is
minimal if and only if every maximal flow `f` saturates all arcs of `(X, X̄)`
(`f(x, y) = c(x, y)`) whereas all arcs of `(X̄, X)` are flowless (`f(x, y) = 0`). -/
theorem minimal_cut_iff_saturated {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) :
    IsMinCut G s t X ↔
      ∀ f : N → N → ℝ, IsMaxFlow G s t f →
        (∀ p ∈ arcsBetween G X Xᶜ, f p.1 p.2 = G.cap p.1 p.2) ∧
        (∀ p ∈ arcsBetween G Xᶜ X, f p.1 p.2 = 0) := by sorry

end FlowsNetworks.MaxFlow
