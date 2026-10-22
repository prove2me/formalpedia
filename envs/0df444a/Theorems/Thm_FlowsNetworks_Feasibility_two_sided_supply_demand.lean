-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_two_sided_supply_demand
-- name    : FlowsNetworks.Feasibility.two_sided_supply_demand
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:18.507409+00:00
-- url     : https://prove2.me/theorems/0da7e9d2-1a2a-44f5-8aaa-ff61fa15a178
-- title:
--   Chapter II, Theorem 2.1 — the supply-demand theorem with lower and upper bounds
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, and let $N$ be partitioned into sources $S$, intermediate nodes $R$ and sinks $T$. Let $0 \le a(x) \le a'(x)$ for $x \in S$ and $0 \le b(x) \le b'(x)$ for $x \in T$. Write $f(x, N)$, $f(N, x)$ for the flow out of and into $x$, $g(X, Y)$ for the sum of $g$ over arcs from $X$ to $Y$, $\bar X = N - X$ and $a(Y) = \sum_{x \in Y} a(x)$.
--
--   Then there is a function $f$ on the arcs satisfying
--   $$\begin{aligned} a(x) \le f(x, N) - f(N, x) &\le a'(x), && x \in S, \\ f(x, N) - f(N, x) &= 0, && x \in R, \\ b(x) \le f(N, x) - f(x, N) &\le b'(x), && x \in T, \\ 0 \le f(x, y) &\le c(x, y), && (x, y) \in \mathcal A, \end{aligned}$$
--   if and only if, for all $X \subseteq N$,
--   $$c(X, \bar X) \ge b(T \cap \bar X) - a'(S \cap \bar X) \quad\text{and}\quad c(X, \bar X) \ge a(S \cap X) - b'(T \cap X).$$
--
--   Here the net outflow at each source and the net inflow at each sink must lie between prescribed limits. With $a = 0$ and $b' = \infty$ the first condition is the condition of the supply-demand theorem (Theorem 1.1).
--
--   **Formalization Note** The partition is three pairwise disjoint `Finset`s with union `univ`; the bound functions are defined on all of $N$ and only their values on $S$ (for $a, a'$) and $T$ (for $b, b'$) enter. All bounds are finite reals. $X$ ranges over all subsets of $N$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 21, Theorem 2.1

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 2.1 (p. 21). With sources `S`,
intermediate nodes `R`, sinks `T`, and bounds `0 ≤ a(x) ≤ a'(x)` on `S`, `0 ≤ b(x) ≤ b'(x)` on `T`,
the constraints (2.1) `a(x) ≤ f(x, N) − f(N, x) ≤ a'(x)` on `S`, (2.2) `f(x, N) − f(N, x) = 0` on
`R`, (2.3) `b(x) ≤ f(N, x) − f(x, N) ≤ b'(x)` on `T`, (2.4) `0 ≤ f ≤ c` on `𝒜` are feasible if and
only if (2.5) `c(X, X̄) ≥ b(T ∩ X̄) − a'(S ∩ X̄)` and (2.6) `c(X, X̄) ≥ a(S ∩ X) − b'(T ∩ X)` hold for
all `X ⊆ N`. -/
theorem two_sided_supply_demand {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a a' b b' : N → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x ∧ a x ≤ a' x) (hb : ∀ x ∈ T, 0 ≤ b x ∧ b x ≤ b' x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x ∧ outflow G f x - inflow G f x ≤ a' x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ b' x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N,
        arcSum G G.cap X Xᶜ ≥ (∑ x ∈ T ∩ Xᶜ, b x) - (∑ x ∈ S ∩ Xᶜ, a' x) ∧
        arcSum G G.cap X Xᶜ ≥ (∑ x ∈ S ∩ X, a x) - (∑ x ∈ T ∩ X, b' x) := by sorry

end FlowsNetworks.Feasibility
