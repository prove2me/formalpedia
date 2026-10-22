-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_minimal_cut_unique_iff
-- name    : FlowsNetworks.MaxFlow.minimal_cut_unique_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:49.965457+00:00
-- url     : https://prove2.me/theorems/277fa61a-8554-4803-9370-56acc123ea1c
-- title:
--   Chapter I, Theorem 5.6 — with positive capacities, the minimal cut is unique iff the source and sink constructions agree
-- statement:
--   Let $[N; \mathcal A]$ be a network whose capacity function is strictly positive, $c(x, y) > 0$ on every arc, let $s \neq t$, and let $f$ be a maximal flow from $s$ to $t$. Let $X$ be the source set of $f$ (smallest set with $s \in X$, closed under: $x \in X$, $f(x, y) < c(x, y)$ $\Rightarrow$ $y \in X$; $x \in X$, $f(y, x) > 0$ $\Rightarrow$ $y \in X$), and let $\bar Y$ be the sink set of $f$ (smallest set with $t \in \bar Y$, closed under: $y \in \bar Y$, $f(x, y) < c(x, y)$ $\Rightarrow$ $x \in \bar Y$; $y \in \bar Y$, $f(y, x) > 0$ $\Rightarrow$ $x \in \bar Y$), with $Y = N - \bar Y$. Then
--   $$\text{the minimal cut } (X, \bar X) \text{ is unique} \iff (X, \bar X) = (Y, \bar Y),$$
--   where "unique" means that every minimal cut $(Z, \bar Z)$ separating $s$ and $t$ has the same arc set as $(X, \bar X)$, and the equality on the right is equality of arc sets.
--
--   This gives a computable test, by two labeling passes from a single maximal flow, of whether the bottleneck of the network is unique. The book remarks right after the theorem that it fails when $c > 0$ is relaxed to $c \ge 0$.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$). Both $X$ and $\bar Y$ are taken relative to the same maximal flow $f$. Cuts are compared as arc sets, as in the book: different node sets can determine the same arc set.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 25, Theorem 5.6 (with Ȳ defined on p. 24)

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network
import Definitions.Def_FlowsNetworks_MaxFlow_AugmentingPath

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 5.6 (p. 25): let `f` be a maximal
flow, `X = sourceSet G f s` the set of nodes defined in the proof of Theorem 5.1, `Ȳ = sinkSet G f t`
the set defined on p. 24 (so `Y` is its complement), and assume that `c` is strictly positive.
The minimal cut `(X, X̄)` is unique (every minimal cut has the same arc set) if and only if the
arc sets `(X, X̄)` and `(Y, Ȳ)` are equal. -/
theorem minimal_cut_unique_iff {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t)
    (hc : ∀ p ∈ G.arcs, 0 < G.cap p.1 p.2)
    (f : N → N → ℝ) (hf : IsMaxFlow G s t f) :
    (∀ Z : Finset N, IsMinCut G s t Z →
        arcsBetween G Z Zᶜ = arcsBetween G (sourceSet G f s) (sourceSet G f s)ᶜ) ↔
      arcsBetween G (sourceSet G f s) (sourceSet G f s)ᶜ =
        arcsBetween G (sinkSet G f t)ᶜ (sinkSet G f t) := by sorry

end FlowsNetworks.MaxFlow
