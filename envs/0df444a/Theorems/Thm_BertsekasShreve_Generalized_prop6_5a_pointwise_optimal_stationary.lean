-- Prove2me | Theorems.Thm_BertsekasShreve_Generalized_prop6_5a_pointwise_optimal_stationary
-- name    : BertsekasShreve.Generalized.prop6_5a_pointwise_optimal_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:55:51.260476+00:00
-- url     : https://prove2.me/theorems/1004dfe9-dbb6-453b-b863-2b4923b025a5
-- title:
--   Proposition 6.5(a) — pointwise optimal policies give an optimal stationary policy in $\tilde\Pi$
-- statement:
--   Consider the generalized abstract model of Section 6.1 under conditions A.1–A.5, Assumption $\tilde C$ and the exact selection assumption. If for each $x\in S$ there is a policy in $\tilde\Pi$ which is optimal at $x$, i.e.
--   $$\forall x\in S\ \exists\pi_x\in\tilde\Pi:\ J_{\pi_x}(x)=J^*(x),$$
--   then there exists an optimal stationary policy $(\mu^*,\mu^*,\dots)\in\tilde\Pi$, i.e. $J_{\mu^*}=J^*$.
--
--   The restricted-class analogue of Proposition 4.3(b): pointwise optimality, possibly by different policies at different states, can be replaced by a single stationary policy from $\tilde M$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 97, Proposition 6.5(a)

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.5(a), p. 97. Under A.1–A.5, Assumption C̃ and the exact selection assumption,
if for each `x ∈ S` there is a policy in `Π̃` which is optimal at `x`, then there is an optimal
stationary policy in `Π̃`. -/
theorem prop6_5a_pointwise_optimal_stationary {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α)
    (hES : P.ExactSelection)
    (hopt : ∀ x, ∃ π : P.Policy, P.IsOptimalAt π x) :
    ∃ μ : P.Sel, P.IsOptimal (P.stationary μ) := by sorry

end BertsekasShreve.Generalized
