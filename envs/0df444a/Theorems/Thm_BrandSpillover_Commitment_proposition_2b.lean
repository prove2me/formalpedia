-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_proposition_2b
-- name    : BrandSpillover.Commitment.proposition_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:02.313179+00:00
-- url     : https://prove2.me/theorems/2d6a5fe7-af12-463d-8c89-3824876ec855
-- title:
--   Proposition 2(b), p. 15 — under (O, O), Firm W's profit decreases in α iff α < (2θ − 2c − 1)/(3(1 − θ))
-- statement:
--   Assume the standing assumptions, and let $\Pi^{oo}_W(a)$ denote Firm W's profit under $(O,O)$ at the CM's optimal prices when the spillover level is $a$. Write
--
--   $$\bar a = \frac{2\theta - 2c - 1}{3(1-\theta)}.$$
--
--   Then, for spillover levels $0 \le a < a' \le 1$:
--
--   1. if $a' \le \bar a$, then $\Pi^{oo}_W(a') < \Pi^{oo}_W(a)$ (the profit is strictly decreasing on $[0, \bar a]$);
--   2. if $\bar a \le a$, then $\Pi^{oo}_W(a) < \Pi^{oo}_W(a')$ (the profit is strictly increasing on $[\bar a, 1]$).
--
--   This is the counterintuitive effect behind Proposition 4: a stronger brand spillover can hurt the firm that benefits from it.
--
--   **Formalization Note** "Decreasing in $\alpha$ if and only if $\alpha < \bar a$" is stated as strict monotonicity on the two sides of $\bar a$; the profit has a kink at $\bar a$, so no derivative is used. Each interval is intersected with $[0,1]$.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 15, Proposition 2(b) (proof App. A, p. 33)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Proposition 2(b), p. 15: under `(O, O)`, Firm W's profit at the CM's optimal prices is
decreasing in the spillover level `α` if and only if `α < (2θ − 2c − 1)/(3(1 − θ))`: it strictly
decreases on `[0, (2θ − 2c − 1)/(3(1 − θ))]` and strictly increases on
`[(2θ − 2c − 1)/(3(1 − θ)), 1]` (each interval intersected with `[0, 1]`). -/
theorem proposition_2b (P : Params) (hP : P.Standing) :
    (∀ (a a' : ℝ) (w w' : ℝ × ℝ), 0 ≤ a → a < a' → a' ≤ 1 →
        a' ≤ (2 * P.θ - 2 * P.c - 1) / (3 * (1 - P.θ)) →
        IsOptPrices P a .OO w → IsOptPrices P a' .OO w' →
        profitW P a' .OO w' < profitW P a .OO w) ∧
    (∀ (a a' : ℝ) (w w' : ℝ × ℝ), 0 ≤ a → a < a' → a' ≤ 1 →
        (2 * P.θ - 2 * P.c - 1) / (3 * (1 - P.θ)) ≤ a →
        IsOptPrices P a .OO w → IsOptPrices P a' .OO w' →
        profitW P a .OO w < profitW P a' .OO w') := by sorry

end BrandSpillover.Commitment
