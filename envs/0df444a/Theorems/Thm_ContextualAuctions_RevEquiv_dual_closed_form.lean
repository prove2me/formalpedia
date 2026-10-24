-- Prove2me | Theorems.Thm_ContextualAuctions_RevEquiv_dual_closed_form
-- name    : ContextualAuctions.RevEquiv.dual_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:45.079904+00:00
-- url     : https://prove2.me/theorems/efb94559-3123-4a67-bea7-8c33d7a9469b
-- title:
--   §3.2, p. 8, last display — closed form of the first-price dual function q^µ(w,B,t)
-- statement:
--   Let $\mu$ be a pacing function, $(w,B)\in\Theta$ a buyer type and $t\ge0$ a dual multiplier. Write $x_\alpha=w^T\alpha/(1+t)$. Then the first-price dual function, defined as the supremum of the Lagrangian over admissible bids, has the closed form
--   $$q^\mu(w,B,t)=(1+t)\,\mathbb E_\alpha\Big[\mathbb 1\{x_\alpha\ge r(\alpha)\}\int_{r(\alpha)}^{x_\alpha}H^\mu_\alpha(s)\,ds\Big]+tB .$$
--
--   This is the first-price side of the key step of Theorem 2: the dual function of every standard auction is shown to equal this same expression.
--
--   **Formalization Note** The left side is the supremum of p. 7 (definition `qDual`), so the identity is a theorem, not a definition. The paper obtains it from Lemma 1 (optimality of $\sigma^\mu_\alpha(x_\alpha)$) and Lemma 6(c) of its online appendix.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 8, §3.2, last display (closed form of q^µ(w,B,t))

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting

namespace ContextualAuctions.RevEquiv

open MeasureTheory

theorem dual_closed_form (M : Model) (hM : M.Standing) (μ : Buyer M → ℝ) (hμ : IsPacing M μ)
    (θ : Buyer M) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t) :
    qDual M μ θ t =
      (1 + t) * ∫ α, (if M.r α ≤ val M θ α / (1 + t) then
        ∫ s in (M.r α)..(val M θ α / (1 + t)), H M μ α s else 0) ∂M.F + t * θ.2 := by sorry

end ContextualAuctions.RevEquiv
