-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_two_sided_iff_one_sided
-- name    : FlowsNetworks.Feasibility.two_sided_iff_one_sided
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:19.079758+00:00
-- url     : https://prove2.me/theorems/47d7df7a-f3cc-4b7b-906c-3edcf3d446ee
-- title:
--   Chapter II, Corollary 2.2 — two-sided bounds are feasible iff both one-sided systems are
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, let $N$ be partitioned into sources $S$, intermediate nodes $R$ and sinks $T$, and let $0 \le a(x) \le a'(x)$ for $x \in S$ and $0 \le b(x) \le b'(x)$ for $x \in T$. Write $f(x, N)$ and $f(N, x)$ for the flow out of and into $x$.
--
--   Then the constraints (2.1)–(2.4)
--   $$\begin{aligned} a(x) \le f(x, N) - f(N, x) &\le a'(x), && x \in S, \\ f(x, N) - f(N, x) &= 0, && x \in R, \\ b(x) \le f(N, x) - f(x, N) &\le b'(x), && x \in T, \\ 0 \le f(x, y) &\le c(x, y), && (x, y) \in \mathcal A, \end{aligned}$$
--   are feasible if and only if each of the two constraint sets
--
--   1. (2.7): $a(x) \le f(x, N) - f(N, x)$ for $x \in S$; $f(x, N) - f(N, x) = 0$ for $x \in R$; $f(N, x) - f(x, N) \le b'(x)$ for $x \in T$; $0 \le f(x, y) \le c(x, y)$ on $\mathcal A$;
--   2. (2.8): $f(x, N) - f(N, x) \le a'(x)$ for $x \in S$; $f(x, N) - f(N, x) = 0$ for $x \in R$; $b(x) \le f(N, x) - f(x, N)$ for $x \in T$; $0 \le f(x, y) \le c(x, y)$ on $\mathcal A$;
--
--   is feasible (each by its own function on the arcs).
--
--   So the lower and the upper bounds can be met by a single flow as soon as the lower bounds at the sources together with the upper bounds at the sinks, and the upper bounds at the sources together with the lower bounds at the sinks, can each be met separately.
--
--   **Formalization Note** The hypotheses $0 \le a \le a'$ on $S$ and $0 \le b \le b'$ on $T$ are those of Theorem 2.1, to which "the constraints (2.1)–(2.4)" refer. The partition is three pairwise disjoint `Finset`s with union `univ`; flows are functions $N \to N \to \mathbb R$ vanishing off $\mathcal A$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 22, Corollary 2.2

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 2.2 (p. 22). Under the hypotheses of
Theorem 2.1 (`0 ≤ a(x) ≤ a'(x)` on `S`, `0 ≤ b(x) ≤ b'(x)` on `T`), the constraints (2.1)–(2.4) are
feasible if and only if each of the constraint sets (2.7) (only the lower bound `a` on `S` and the
upper bound `b'` on `T`) and (2.8) (only the upper bound `a'` on `S` and the lower bound `b` on
`T`) is feasible. -/
theorem two_sided_iff_one_sided {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (S R T : Finset N) (hpart : IsPartition S R T)
    (a a' b b' : N → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x ∧ a x ≤ a' x) (hb : ∀ x ∈ T, 0 ≤ b x ∧ b x ≤ b' x) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x ∧ outflow G f x - inflow G f x ≤ a' x) ∧
        (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
        (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ b' x) ∧
        (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, a x ≤ outflow G f x - inflow G f x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, inflow G f x - outflow G f x ≤ b' x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ∧
        (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
          (∀ x ∈ S, outflow G f x - inflow G f x ≤ a' x) ∧
          (∀ x ∈ R, outflow G f x - inflow G f x = 0) ∧
          (∀ x ∈ T, b x ≤ inflow G f x - outflow G f x) ∧
          (∀ p ∈ G.arcs, 0 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) := by sorry

end FlowsNetworks.Feasibility
