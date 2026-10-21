-- Prove2me | Theorems.Thm_FlowsNetworks_MaxFlow_max_flow_min_cut
-- name    : FlowsNetworks.MaxFlow.max_flow_min_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:04.27598+00:00
-- url     : https://prove2.me/theorems/95b40360-b26c-4ea2-9bc5-baaa182e39c7
-- title:
--   Chapter I, Theorem 5.1 — max flow min cut theorem
-- statement:
--   Let $[N; \mathcal A]$ be a network: a finite set $N$ of nodes and a set $\mathcal A$ of ordered pairs $(x, y)$, $x \neq y$, of nodes, each arc carrying a nonnegative real capacity $c(x, y)$. Let $s \neq t$ be two distinguished nodes. A flow of value $v$ from $s$ to $t$ is a function $f \ge 0$ on the arcs with $f \le c$ and net flow $v$ out of $s$, $-v$ out of $t$ and $0$ out of every other node; a cut separating $s$ and $t$ is the set $(X, \bar X)$ of arcs leading from a node set $X \ni s$ to its complement $\bar X \ni t$, and its capacity is $c(X, \bar X)$.
--
--   **Max flow min cut theorem.** For any network the maximal flow value from $s$ to $t$ is equal to the minimal cut capacity over cuts separating $s$ and $t$:
--   $$\max\{v : \text{there is a flow of value } v \text{ from } s \text{ to } t\} \;=\; \min\{c(X, \bar X) : s \in X,\ t \notin X\},$$
--   and both the maximum and the minimum are attained.
--
--   This is the central theorem of network flow theory: it is a combinatorial instance of linear programming duality, and the later chapters of the book derive from it the supply–demand and circulation theorems, the König–Egerváry and Menger theorems, and Hall's theorem on systems of distinct representatives.
--
--   **Formalization Note** The book's "two distinguished nodes" $s, t$ are assumed distinct ($s \neq t$); for $s = t$ there would be no cut. The statement asserts one real number $v$ that is the greatest element of the set of flow values and the least element of the set of cut capacities, so the existence of a maximal flow and of a minimal cut is part of the claim; no supremum or infimum with a default value is used. Cuts are given by their node sets $X$, and $c(X, \bar X)$ sums the capacities over the arcs from $X$ to $\bar X$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 19, Theorem 5.1

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

/-- Ford–Fulkerson, *Flows in Networks*, Chapter I, Theorem 5.1 (max flow min cut theorem, p. 19):
for any network the maximal flow value from `s` to `t` is equal to the minimal cut capacity over
cuts separating `s` and `t`. Both extrema are attained: there is a number `v` that is the value
of some flow and at least the value of every flow, and that is the capacity of some cut and at
most the capacity of every cut. -/
theorem max_flow_min_cut {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (s t : N) (hst : s ≠ t) :
    ∃ v : ℝ,
      IsGreatest {w : ℝ | ∃ f : N → N → ℝ, IsFlow G s t f w} v ∧
      IsLeast {κ : ℝ | ∃ X : Finset N, s ∈ X ∧ t ∉ X ∧ κ = cutCapacity G X} v := by sorry

end FlowsNetworks.MaxFlow
