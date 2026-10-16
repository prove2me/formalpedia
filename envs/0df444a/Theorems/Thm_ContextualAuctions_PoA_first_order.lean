-- Prove2me | Theorems.Thm_ContextualAuctions_PoA_first_order
-- name    : ContextualAuctions.PoA.first_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:51.229398+00:00
-- url     : https://prove2.me/theorems/856c6af7-4991-4aa0-aa8c-89b276c427a4
-- title:
--   §3.2, p. 9 — primal feasibility and complementary slackness
-- statement:
--   Fix a model with zero reserves, a pacing function $\mu$, and buyer type $(w,B)\in\Theta$. If $t^*\ge0$ minimizes the buyer's dual function $q^\mu(w,B,t)$ over $t\ge0$, the corresponding bid $b_{t^*}(\alpha)=\sigma^\mu_\alpha(w^\top\alpha/(1+t^*))$ spends at most the buyer's budget, and the multiplier vanishes unless the budget is exhausted:
--   $$
--   P^\mu(b_{t^*})\le B,\qquad t^*\bigl(B-P^\mu(b_{t^*})\bigr)=0.
--   $$
--   These are primal feasibility and complementary slackness for the first-price buyer problem.
--
--   **Formalization Note** The statement specializes the paper's §3.2 conditions to the zero-reserve regime of §5. Membership of $t^*$ in $[0,\infty)$ is explicit because minimization on a set alone does not assert it.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 9, §3.2, opening display

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_Setting

namespace ContextualAuctions.PoA

open MeasureTheory

/-- §3.2, printed p. 9: dual optimality yields feasibility and complementary slackness. -/
theorem first_order (M : Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (θ : Buyer M) (hθ : θ ∈ Theta M) (tstar : ℝ)
    (ht : 0 ≤ tstar) (hmin : IsMinOn (qDual M μ θ) (Set.Ici 0) tstar) :
    payment M (beta M μ) (bidAt M μ θ tstar) ≤ θ.2 ∧
      tstar * (θ.2 - payment M (beta M μ) (bidAt M μ θ tstar)) = 0 := by sorry

end ContextualAuctions.PoA
