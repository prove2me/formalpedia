-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_stationary_optimal_policies
-- name    : BertsekasShreve.Contraction.stationary_optimal_policies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:16.174987+00:00
-- url     : https://prove2.me/theorems/8673759e-0ffb-454c-8a01-41e45dfeda7b
-- title:
--   Proposition 4.3 — characterization and existence of stationary optimal and $\varepsilon$-optimal policies
-- statement:
--   Let Assumption C hold. Then:
--
--   1. A stationary policy $\pi^*=(\mu^*,\mu^*,\dots)$ is optimal ($J_{\mu^*}=J^*$) if and only if
--   $$T_{\mu^*}(J^*)=T(J^*),$$
--   and, equivalently, if and only if $T_{\mu^*}(J_{\mu^*})=T(J_{\mu^*})$.
--   2. If for each $x\in S$ there exists a policy that is optimal at $x$ (that is, $J_\pi(x)=J^*(x)$ for some $\pi$ depending on $x$), then there exists a stationary optimal policy.
--   3. For every $\varepsilon>0$ there exists a stationary policy $(\mu_\varepsilon,\mu_\varepsilon,\dots)$ with
--   $$\|J^*-J_{\mu_\varepsilon}\|\le\varepsilon.$$
--
--   Part 1 reduces the search for stationary optimal policies to the attainment of the infimum in Bellman's equation $J^*(x)=\inf_{u\in U(x)}H(x,u,J^*)$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 56, Proposition 4.3

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.3, p. 56. Under Assumption C:
(a) a stationary policy `(μ*, μ*, …)` is optimal (`J_{μ*} = J*`) iff `T_{μ*}(J*) = T(J*)`, and
equivalently iff `T_{μ*}(J_{μ*}) = T(J_{μ*})`;
(b) if for each `x` some policy is optimal at `x`, there is a stationary optimal policy;
(c) for every `ε > 0` there is a stationary policy `(μ_ε, μ_ε, …)` with `‖J* − J_{μ_ε}‖ ≤ ε`. -/
theorem stationary_optimal_policies {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ μs : P.Selector,
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs P.Jstar = P.T P.Jstar) ∧
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs (P.Jmu μs) = P.T (P.Jmu μs))) ∧
    ((∀ x : S, ∃ π : P.Policy, P.Jpi π x = P.Jstar x) →
      ∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ με : P.Selector, SupDistLe P.Jstar (P.Jmu με) ε) := by sorry

end BertsekasShreve.Contraction
