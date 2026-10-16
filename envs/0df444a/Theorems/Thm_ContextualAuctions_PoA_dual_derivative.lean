-- Prove2me | Theorems.Thm_ContextualAuctions_PoA_dual_derivative
-- name    : ContextualAuctions.PoA.dual_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:43.872893+00:00
-- url     : https://prove2.me/theorems/b019cc5c-8d7b-4ace-947d-7c04e7443460
-- title:
--   §3.2, p. 8 — derivative of the dual function
-- statement:
--   Fix a model with zero reserve prices, a pacing function $\mu$, a buyer type $(w,B)\in\Theta$, and a nonnegative dual multiplier $t$. Let $b_t(\alpha)=\sigma^\mu_\alpha(w^\top\alpha/(1+t))$, and let $P^\mu(b_t)$ be the expected first-price expenditure against buyers bidding $\beta^\mu$. The dual function from the buyer's optimization problem satisfies the right-sided derivative identity at the boundary and the usual derivative identity in the interior:
--   $$
--   \frac{\partial q^\mu(w,B,t)}{\partial t}=B-P^\mu(b_t).
--   $$
--   This relates dual optimality to budget feasibility.
--
--   **Formalization Note** The theorem uses the zero-reserve specialization needed by §5. The derivative is stated within $[0,\infty)$, so it includes $t=0$. The paper's dual remains a supremum over admissible bids.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 8, §3.2, paragraph after Proposition 1

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_Setting

namespace ContextualAuctions.PoA

open MeasureTheory

/-- §3.2, printed p. 8: the dual derivative is budget minus expected expenditure. -/
theorem dual_derivative (M : Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (θ : Buyer M) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (qDual M μ θ)
      (θ.2 - payment M (beta M μ) (bidAt M μ θ t)) (Set.Ici 0) t := by sorry

end ContextualAuctions.PoA
