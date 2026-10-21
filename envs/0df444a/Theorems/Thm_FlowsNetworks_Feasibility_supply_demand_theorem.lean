-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_supply_demand_theorem
-- name    : FlowsNetworks.Feasibility.supply_demand_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:19.021567+00:00
-- url     : https://prove2.me/theorems/3b608198-a0f0-4eea-b087-757be7e6536c
-- title:
--   Chapter II, Theorem 1.1 — Gale's supply-demand theorem
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, and let $N$ be partitioned into sources $S$, intermediate nodes $R$ and sinks $T$. Each source $x \in S$ has a **supply** $a(x) \ge 0$ and each sink $x \in T$ a **demand** $b(x) \ge 0$. Write $f(x, N)$ and $f(N, x)$ for the flow out of and into $x$, $g(X, Y)$ for the sum of $g$ over arcs from $X$ to $Y$, $\bar X = N - X$, and $a(Y) = \sum_{x \in Y} a(x)$.
--
--   Then there is a function $f$ on the arcs satisfying
--   $$\begin{aligned} f(x, N) - f(N, x) &\le a(x), && x \in S, \\ f(x, N) - f(N, x) &= 0, && x \in R, \\ f(N, x) - f(x, N) &\ge b(x), && x \in T, \\ 0 \le f(x, y) &\le c(x, y), && (x, y) \in \mathcal A, \end{aligned}$$
--   if and only if
--   $$b(T \cap \bar X) - a(S \cap \bar X) \le c(X, \bar X) \quad \text{for every subset } X \subseteq N.$$
--
--   This is the supply-demand theorem of Gale (1957): the demands can be met from the supplies exactly when the net demand of no node set exceeds the capacity of the arcs leading into it.
--
--   **Formalization Note** The partition is three `Finset`s, pairwise disjoint with union `univ`. Supplies and demands are functions on all of $N$; only their values on $S$ and $T$ enter (through the sums over $S \cap \bar X$ and $T \cap \bar X$), and they are assumed nonnegative there. $X$ ranges over all subsets of $N$, including $\emptyset$ and $N$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 1.1 (Gale's supply-demand theorem,
p. 4). The node set is partitioned into sources `S`, intermediate nodes `R` and sinks `T`; each
source `x` has a supply `a(x) ≥ 0` and each sink `x` a demand `b(x) ≥ 0`. The constraints
(1.1) `f(x, N) − f(N, x) ≤ a(x)` on `S`, (1.2) `f(x, N) − f(N, x) = 0` on `R`,
(1.3) `f(N, x) − f(x, N) ≥ b(x)` on `T`, (1.4) `0 ≤ f ≤ c` on `𝒜` are feasible if and only if
(1.5) `b(T ∩ X̄) − a(S ∩ X̄) ≤ c(X, X̄)` for every subset `X ⊆ N`. -/
theorem supply_demand_theorem {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a b : N → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ x ∈ T, 0 ≤ b x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, outflow G f x - inflow G f x ≤ a x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, inflow G f x - outflow G f x ≥ b x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N,
        (∑ x ∈ T ∩ Xᶜ, b x) - (∑ x ∈ S ∩ Xᶜ, a x) ≤ arcSum G G.cap X Xᶜ := by sorry

end FlowsNetworks.Feasibility
