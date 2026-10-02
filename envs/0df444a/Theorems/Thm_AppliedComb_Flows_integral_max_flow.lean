-- Prove2me | Theorems.Thm_AppliedComb_Flows_integral_max_flow
-- name    : AppliedComb.Flows.integral_max_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:41:14.045155+00:00
-- url     : https://prove2.me/theorems/a7e32414-c770-4cba-8085-8f5b60781838
-- title:
--   Theorem 14.1 — integer capacities admit an integer maximum flow
-- statement:
--   Let $G$ be a network in which every edge has integer capacity: $c(x, y) \in \mathbb Z$ for every edge $(x, y)$. Then there is a maximum flow in which every edge carries an integer amount of flow: a flow $\phi$ with
--   $$\operatorname{value}(\psi) \le \operatorname{value}(\phi) \ \text{ for every flow } \psi, \qquad \phi(x, y) \in \mathbb Z \ \text{ for every edge } (x, y).$$
--
--   The theorem does not say that every maximum flow is integral, only that one is. With capacities all equal to $1$ it turns flow problems into combinatorial problems (matchings, chain partitions). The book states it without proof.
--
--   **Formalization Note.** Networks and flows are those of `AppliedComb.Flows.Network`; the flow is real-valued and its integrality is asserted on edges (on non-edges it is $0$ by the definition of a flow).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 279, Theorem 14.1

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network

namespace AppliedComb.Flows

/-- **Theorem 14.1** (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 279). In a
network flow problem in which every edge has integer capacity, there is a maximum flow in which
every edge carries an integer amount of flow: a flow `ϕ` whose value is at least the value of
every flow, with `ϕ(x, y) ∈ ℤ` for every edge `(x, y)`. -/
theorem integral_max_flow {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : ∀ x y, N.adj x y → ∃ n : ℤ, N.cap x y = n) :
    ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧
      (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ) ∧
      ∀ x y, N.adj x y → ∃ n : ℤ, ϕ x y = n := by sorry

end AppliedComb.Flows
