-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_sourceSet_subset_minimal_cut
-- name    : FlowsNetworks.MaxFlow.sourceSet_subset_minimal_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:49.505878+00:00
-- url     : https://prove2.me/theorems/858e46a4-7216-4c91-9ec1-4c101cce59ce
-- title:
--   Chapter I, Theorem 5.5 — the minimal cut of the labeling proof has the smallest source set
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$ and let $s \neq t$. Let $(Y, \bar Y)$ be any minimal cut separating $s$ and $t$, let $f$ be a maximal flow from $s$ to $t$, and let $X$ be the source set of $f$: the smallest set of nodes containing $s$ such that $x \in X$ and $f(x, y) < c(x, y)$ imply $y \in X$, and $x \in X$ and $f(y, x) > 0$ imply $y \in X$ (so $(X, \bar X)$ is the minimal cut defined relative to $f$ in the proof of Theorem 5.1). Then
--   $$X \subseteq Y.$$
--
--   Consequently $X$ is the intersection of the source sides of all minimal cuts and does not depend on the choice of the maximal flow $f$.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). The set $X$ is defined explicitly by rules (a), (b) (the definition `sourceSet`); that $(X, \bar X)$ is a minimal cut is not assumed.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 23, Theorem 5.5

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
import Definitions.Def_FlowsNetworks_MaxFlow_AugmentingPath

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 5.5 (p. 23): let `(Y, Ȳ)` be any
minimal cut, let `f` be a maximal flow, and let `(X, X̄)` be the minimal cut defined relative to
`f` in the proof of Theorem 5.1 (`X = sourceSet G f s`). Then `X ⊆ Y`. -/
theorem sourceSet_subset_minimal_cut {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) (Y : Finset N) (hY : IsMinCut G s t Y)
    (f : N → N → ℝ) (hf : IsMaxFlow G s t f) :
    sourceSet G f s ⊆ Y := by sorry

end FlowsNetworks.MaxFlow
