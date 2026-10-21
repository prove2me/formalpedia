-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_circulation_node_bounds
-- name    : FlowsNetworks.Feasibility.circulation_node_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:27.727997+00:00
-- url     : https://prove2.me/theorems/7d2db906-c70a-4439-a42e-c9ac5e6f0037
-- title:
--   Chapter II, Theorem 3.2 — circulations with bounds on the net inflow at every node
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, let $\ell$ be a lower bound function on the arcs with $0 \le \ell(x, y) \le c(x, y)$ for every $(x, y) \in \mathcal A$, and let $a, a'$ be real functions on the nodes with $a(x) \le a'(x)$ for every $x \in N$ (no sign condition). Write $f(x, N)$ and $f(N, x)$ for the flow out of and into $x$, $g(X, Y)$ for the sum of $g$ over the arcs from $X$ to $Y$, $\bar X = N - X$, and $a(X) = \sum_{x \in X} a(x)$.
--
--   Then there is a function $f$ on the arcs satisfying
--   $$a(x) \le f(N, x) - f(x, N) \le a'(x) \quad (x \in N), \qquad \ell(x, y) \le f(x, y) \le c(x, y) \quad ((x, y) \in \mathcal A),$$
--   if and only if
--   $$c(X, \bar X) \ge \ell(\bar X, X) + \max\,[\,a(\bar X),\ -a'(X)\,] \quad \text{for all } X \subseteq N.$$
--
--   This extension of the circulation theorem, also due to Hoffman, prescribes limits on the net flow into each node; with $a = a' = 0$ it is the circulation theorem.
--
--   **Formalization Note** Note the sign convention: the node bounds are on the net *inflow* $f(N, x) - f(x, N)$, as in the book's (3.4). $X$ ranges over all subsets of $N$, including $\emptyset$ and $N$. Flows are functions $N \to N \to \mathbb R$ vanishing off $\mathcal A$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 28, Theorem 3.2

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 3.2 (Hoffman's extension, p. 28). Let
`a(x) ≤ a'(x)` at every node (no sign condition) and `0 ≤ ℓ(x, y) ≤ c(x, y)` on every arc. The
constraints (3.4) `a(x) ≤ f(N, x) − f(x, N) ≤ a'(x)` at every node and (3.5) `ℓ(x, y) ≤ f(x, y) ≤
c(x, y)` on every arc are feasible if and only if (3.6)
`c(X, X̄) ≥ ℓ(X̄, X) + max [a(X̄), −a'(X)]` holds for all `X ⊆ N`. -/
theorem circulation_node_bounds {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (ℓ : N → N → ℝ) (a a' : N → ℝ)
    (ha : ∀ x, a x ≤ a' x)
    (hℓ : ∀ p ∈ G.arcs, 0 ≤ ℓ p.1 p.2 ∧ ℓ p.1 p.2 ≤ G.cap p.1 p.2) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x, a x ≤ inflow G f x - outflow G f x ∧ inflow G f x - outflow G f x ≤ a' x) ∧
        (∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N,
        arcSum G G.cap X Xᶜ ≥ arcSum G ℓ Xᶜ X + max (∑ x ∈ Xᶜ, a x) (-(∑ x ∈ X, a' x)) := by sorry

end FlowsNetworks.Feasibility
