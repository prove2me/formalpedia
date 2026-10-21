-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_proposition_2a
-- name    : BOGOPromo.NoStockpile.proposition_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:36.270488+00:00
-- url     : https://prove2.me/theorems/7925cd73-eae1-4219-b9a8-050cdcfdeee1
-- title:
--   Proposition 2 a), p. 16 (PDF 16) — for c < c̃(θ) the BOGO-NSP equilibrium is the BOGO of Table 3
-- statement:
--   Let $0<\theta\le 1$ and $0\le c<\tilde c(\theta)=\theta-(1-\theta)\sqrt{2\theta/(1+2\theta)}$. In the BOGO game an equilibrium exists, and in every equilibrium the wholesale price is
--   $$w^*=\frac{3\theta+c+2c\theta}{2(1+2\theta)},$$
--   the retailer offers the BOGO with
--   $$p_b^*=\frac{2+c+\theta(7+2c)}{4(1+2\theta)},\qquad p_g^*=\frac{c(1+2\theta)+\theta(5+4\theta)}{4(1+2\theta)},$$
--   the demand is $D^*=\dfrac{3\theta-c-2c\theta}{4\theta}$, the retailer's profit is $\dfrac{\theta(8-7\theta+8\theta^2)+(1+2\theta)(c^2(1+2\theta)-6c\theta)}{16\theta(1+2\theta)}$, and the manufacturer's profit is $\dfrac{(3\theta-c-2c\theta)^2}{8\theta(1+2\theta)}$.
--
--   **Formalization Note** Only part a) of Proposition 2 is formalized; part b) is not needed by Corollary 4, and at $c=\tilde c(\theta)$ the manufacturer is indifferent between the BOGO and no-promotion outcomes.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 16 (PDF 16), Proposition 2 a) and Table 3 (3rd column)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem proposition_2a (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cTilde θ) :
    (∃ (w : ℝ) (r : ℝ → BPolicy), IsEqB θ c w r) ∧
    ∀ (w : ℝ) (r : ℝ → BPolicy), IsEqB θ c w r →
      w = (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ)) ∧
      r w = .bogo ((2 + c + θ * (7 + 2 * c)) / (4 * (1 + 2 * θ)))
        ((c * (1 + 2 * θ) + θ * (5 + 4 * θ)) / (4 * (1 + 2 * θ))) ∧
      (r w).demand θ = (3 * θ - c - 2 * c * θ) / (4 * θ) ∧
      (r w).profit θ w = (θ * (8 - 7 * θ + 8 * θ ^ 2) + (1 + 2 * θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ)) ∧
      (w - c) * (r w).demand θ = (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) := by sorry

end BOGOPromo.NoStockpile
