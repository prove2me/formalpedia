-- Prove2me | Theorems.Thm_FlowsNetworks_Feasibility_circulation_theorem
-- name    : FlowsNetworks.Feasibility.circulation_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:25.068176+00:00
-- url     : https://prove2.me/theorems/13f23fca-e1ca-49c8-b94a-3decb9375ee4
-- title:
--   Chapter II, Theorem 3.1 — Hoffman's circulation theorem
-- statement:
--   Let $[N; \mathcal A]$ be a network with nonnegative arc capacities $c$, and let $\ell$ be a lower bound function on the arcs with $0 \le \ell(x, y) \le c(x, y)$ for every $(x, y) \in \mathcal A$. Write $f(x, N)$ and $f(N, x)$ for the flow out of and into the node $x$, $g(X, Y)$ for the sum of $g$ over the arcs from $X$ to $Y$, and $\bar X = N - X$.
--
--   Then there is a function $f$ on the arcs (a **feasible circulation**) satisfying
--   $$f(x, N) - f(N, x) = 0 \quad (x \in N), \qquad \ell(x, y) \le f(x, y) \le c(x, y) \quad ((x, y) \in \mathcal A),$$
--   if and only if
--   $$c(X, \bar X) \ge \ell(\bar X, X) \quad \text{for all } X \subseteq N.$$
--
--   This is Hoffman's circulation theorem (1960): a flow that is conserved at every node and respects lower and upper bounds on every arc exists exactly when, for every node set, the capacity of the arcs leaving it is at least the lower bounds on the arcs entering it.
--
--   **Formalization Note** Flows are functions $N \to N \to \mathbb R$ vanishing off $\mathcal A$ (`SupportedOnArcs`); feasibility is the existence of such a function with the two displayed properties, not a definition by the cut condition. $X$ ranges over all subsets of $N$ (`Finset N`), with $\bar X$ its complement; the conditions for $X = \emptyset$ and $X = N$ hold trivially.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 26, Theorem 3.1

import Mathlib
import Definitions.Def_FlowsNetworks_Feasibility_Network

namespace FlowsNetworks.Feasibility

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 3.1 (Hoffman's circulation theorem,
p. 26). Let `ℓ` be a lower bound function on the arcs with `0 ≤ ℓ(x, y) ≤ c(x, y)`. The constraints
(3.1) `f(x, N) − f(N, x) = 0` for every node `x` and (3.2) `ℓ(x, y) ≤ f(x, y) ≤ c(x, y)` on every
arc are feasible if and only if (3.3) `c(X, X̄) ≥ ℓ(X̄, X)` holds for all `X ⊆ N`. -/
theorem circulation_theorem {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (ℓ : N → N → ℝ)
    (hℓ : ∀ p ∈ G.arcs, 0 ≤ ℓ p.1 p.2 ∧ ℓ p.1 p.2 ≤ G.cap p.1 p.2) :
    (∃ f : N → N → ℝ, SupportedOnArcs G f ∧
        (∀ x, outflow G f x - inflow G f x = 0) ∧
        (∀ p ∈ G.arcs, ℓ p.1 p.2 ≤ f p.1 p.2 ∧ f p.1 p.2 ≤ G.cap p.1 p.2)) ↔
      ∀ X : Finset N, arcSum G G.cap X Xᶜ ≥ arcSum G ℓ Xᶜ X := by sorry

end FlowsNetworks.Feasibility
