-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_quantity_game
-- name    : BrandSpillover.Commitment.quantity_game
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:53.609817+00:00
-- url     : https://prove2.me/theorems/f50cd5e4-1db3-4470-b3c3-8994e78670bb
-- title:
--   §4.1–4.2, pp. 11–12 — the first-order-condition quantities are the unique Nash equilibrium of the quantity game
-- statement:
--   Consider the quantity stage with Firm W's brand power $\theta_W$ and unit costs $k_S$ (Firm S) and $k_W$ (Firm W). Firm S's profit from quantity $x$ when Firm W produces $y$ is $(1 - x - y - k_S)x$, and Firm W's profit from $y$ is $(\theta_W - x - y - k_W)y$. Let
--
--   $$q_S = \tfrac13(2 - \theta_W - 2k_S + k_W),\qquad q_W = \tfrac13(2\theta_W - 1 + k_S - 2k_W).$$
--
--   Then:
--
--   1. $(q_S, q_W)$ is a Nash equilibrium of this game with quantities ranging over $\mathbb R$;
--   2. it is the only one;
--   3. each firm's equilibrium profit is the square of its quantity: $\Pi_S = q_S^2$ and $\Pi_W = q_W^2$.
--
--   This ties the closed-form quantities used throughout the paper to the quantity game they solve, and gives the squared-quantity profit formulas used in all later comparisons.
--
--   **Formalization Note** Quantities range over all real numbers, matching the paper's first-order-condition derivation.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 11 (§4.1) and p. 12 (§4.2); App. A, p. 31

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- §4.1, p. 11, and §4.2, p. 12: the first-order-condition quantities are the unique Nash
equilibrium of the stage-4 quantity game on `ℝ`, and each firm's equilibrium profit is the square
of its quantity. -/
theorem quantity_game (θW kS kW : ℝ) :
    IsQuantityNE θW kS kW (focQS θW kS kW) (focQW θW kS kW) ∧
    (∀ x y : ℝ, IsQuantityNE θW kS kW x y → x = focQS θW kS kW ∧ y = focQW θW kS kW) ∧
    SupplierAudit.Competition.cournotPayoff 1 1 kS (focQS θW kS kW) (focQW θW kS kW) =
      focQS θW kS kW ^ 2 ∧
    SupplierAudit.Competition.cournotPayoff 1 θW kW (focQW θW kS kW) (focQS θW kS kW) =
      focQW θW kS kW ^ 2 := by sorry

end BrandSpillover.Commitment
