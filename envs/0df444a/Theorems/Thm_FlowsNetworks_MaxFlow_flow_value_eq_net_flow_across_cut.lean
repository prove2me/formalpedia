-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_flow_value_eq_net_flow_across_cut
-- name    : FlowsNetworks.MaxFlow.flow_value_eq_net_flow_across_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:01.218984+00:00
-- url     : https://prove2.me/theorems/c8b6f505-c5c8-4bae-9e5e-8fc969f75329
-- title:
--   Chapter I, Lemma 4.1 — the value of a flow is the net flow across any cut, and at most its capacity
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative capacities $c$, let $s, t$ be nodes, and let $f$ be a flow from $s$ to $t$ of value $v$. If $X \subseteq N$ with $s \in X$ and $t \in \bar X = N - X$, so that $(X, \bar X)$ is a cut separating $s$ and $t$, then
--   $$v = f(X, \bar X) - f(\bar X, X) \le c(X, \bar X). \qquad (4.1)$$
--   Here $g(X, Y)$ denotes the sum of $g$ over the arcs leading from $X$ to $Y$.
--
--   In words, the value of a flow equals the net flow across any cut separating source and sink, and therefore never exceeds the capacity of the cut: this is the easy inequality "max flow $\le$ min cut".
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 18, Lemma 4.1

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Lemma 4.1 (p. 18): if `f` is a flow from `s`
to `t` of value `v` and `(X, X̄)` is a cut separating `s` and `t`, then
(4.1) `v = f(X, X̄) − f(X̄, X) ≤ c(X, X̄)`. -/
theorem flow_value_eq_net_flow_across_cut {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (f : N → N → ℝ) (v : ℝ) (hf : IsFlow G s t f v)
    (X : Finset N) (hs : s ∈ X) (ht : t ∉ X) :
    v = arcSum G f X Xᶜ - arcSum G f Xᶜ X ∧
      arcSum G f X Xᶜ - arcSum G f Xᶜ X ≤ cutCapacity G X := by sorry

end FlowsNetworks.MaxFlow
