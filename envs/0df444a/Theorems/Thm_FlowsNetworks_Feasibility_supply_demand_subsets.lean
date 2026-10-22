-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_supply_demand_subsets
-- name    : FlowsNetworks.Feasibility.supply_demand_subsets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:16.609415+00:00
-- url     : https://prove2.me/theorems/e19fea35-fb1d-4cef-8b50-e1c59079b939
-- title:
--   Chapter II, Corollary 1.2 — feasibility from feasibility for every set of sinks
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, let $N$ be partitioned into sources $S$, intermediate nodes $R$ and sinks $T$, and let $a(x) \ge 0$ ($x \in S$) be supplies and $b(x) \ge 0$ ($x \in T$) demands. Number the constraints on a function $f$ on the arcs:
--
--   1. (1.1) $f(x, N) - f(N, x) \le a(x)$ for $x \in S$;
--   2. (1.2) $f(x, N) - f(N, x) = 0$ for $x \in R$;
--   3. (1.3) $f(N, x) - f(x, N) \ge b(x)$ for $x \in T$;
--   4. (1.4) $0 \le f(x, y) \le c(x, y)$ for $(x, y) \in \mathcal A$.
--
--   Then (1.1)–(1.4) are feasible if and only if for every set $T' \subseteq T$ there is a function $f_{T'}$ on the arcs satisfying (1.1), (1.2), (1.4) and
--   $$f_{T'}(N, T') - f_{T'}(T', N) \ge b(T'),$$
--   where $g(X, Y)$ is the sum of $g$ over arcs from $X$ to $Y$ and $b(T') = \sum_{x \in T'} b(x)$.
--
--   The corollary says that the demands can be met simultaneously as soon as the aggregate demand of every set of sinks can be met on its own.
--
--   **Formalization Note** The partition is three pairwise disjoint `Finset`s with union `univ`; supplies and demands are functions on $N$, nonnegative on $S$ and $T$. $T'$ ranges over all subsets of $T$, including $\emptyset$ and $T$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 7, Corollary 1.2

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 1.2 (p. 7). With sources `S`,
intermediate nodes `R`, sinks `T`, supplies `a(x) ≥ 0` on `S` and demands `b(x) ≥ 0` on `T`, the
constraints (1.1)–(1.4) are feasible if and only if, for every set `T' ⊆ T`, there is a flow
`f_{T'}` satisfying (1.1), (1.2), (1.4) and (1.6) `f_{T'}(N, T') − f_{T'}(T', N) ≥ b(T')`. -/
theorem supply_demand_subsets {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a b : N → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ x ∈ T, 0 ≤ b x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, outflow G f x - inflow G f x ≤ a x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, inflow G f x - outflow G f x ≥ b x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ T' : Finset N, T' ⊆ T →
        ∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, outflow G f x - inflow G f x ≤ a x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2) ∧
          arcSum G f Finset.univ T' - arcSum G f T' Finset.univ ≥ ∑ x ∈ T', b x := by sorry

end FlowsNetworks.Feasibility
