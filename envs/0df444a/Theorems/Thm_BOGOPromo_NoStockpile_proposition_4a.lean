-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_proposition_4a
-- name    : BOGOPromo.NoStockpile.proposition_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:42.725565+00:00
-- url     : https://prove2.me/theorems/4ed2dab2-b9ba-4be1-b401-e144c9bc2d2b
-- title:
--   Proposition 4 a), p. 21 (PDF 21) — for c < c̄(θ) the PR-NSP equilibrium is the price reduction of Table 3
-- statement:
--   Let $0<\theta\le 1$ and $0\le c<\bar c(\theta)=\dfrac{\theta(4\theta-1)}{1+2\theta}-2(1-\theta)\sqrt{\dfrac{\theta}{1+\theta}}$. In the PR game an equilibrium exists, and in every equilibrium the wholesale price is
--   $$w^*=\frac{3\theta+c+2c\theta}{2(1+2\theta)},$$
--   the retailer offers the price reduction with
--   $$p_r^*=\frac{2+c+\theta(7+2c)}{4(1+2\theta)},\qquad p_d^*=\frac{c+\theta(7+3c)+\theta^2(11+2c)}{4(1+2\theta)(1+\theta)},$$
--   the demand is $D^*=\dfrac{3\theta-c-2c\theta}{4\theta}$, the retailer's profit is $\dfrac{\theta(4+\theta+13\theta^2)+(1+2\theta)(1+\theta)(c^2(1+2\theta)-6c\theta)}{16\theta(1+2\theta)(1+\theta)}$, and the manufacturer's profit is $\dfrac{(3\theta-c-2c\theta)^2}{8\theta(1+2\theta)}$.
--
--   **Formalization Note** Only part a) of Proposition 4 is formalized. Part b) of the page (a single price for $\bar c(\theta)\le c\le 1$) does not hold as an equilibrium statement: at $w=\bar\theta$ the retailer is indifferent between the price reduction and the single price, the price reduction sells more, and above $\bar c(\theta)$ the manufacturer can gain by setting $w$ at or just below $\bar\theta$ (for $\theta=4/5$, $c=1/2$: $5/72>1/16$). Corollary 4 uses only part a).
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 21 (PDF 21), Proposition 4 a) and Table 3 (4th column)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem proposition_4a (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hc0 : 0 ≤ c) (hc : c < cBar θ) :
    (∃ (w : ℝ) (r : ℝ → PPolicy), IsEqP θ c w r) ∧
    ∀ (w : ℝ) (r : ℝ → PPolicy), IsEqP θ c w r →
      w = (3 * θ + c + 2 * c * θ) / (2 * (1 + 2 * θ)) ∧
      r w = .priceRed ((2 + c + θ * (7 + 2 * c)) / (4 * (1 + 2 * θ)))
        ((c + θ * (7 + 3 * c) + θ ^ 2 * (11 + 2 * c)) / (4 * (1 + 2 * θ) * (1 + θ))) ∧
      (r w).demand θ = (3 * θ - c - 2 * c * θ) / (4 * θ) ∧
      (r w).profit θ w = (θ * (4 + θ + 13 * θ ^ 2) +
          (1 + 2 * θ) * (1 + θ) * (c ^ 2 * (1 + 2 * θ) - 6 * c * θ)) /
        (16 * θ * (1 + 2 * θ) * (1 + θ)) ∧
      (w - c) * (r w).demand θ = (3 * θ - c - 2 * c * θ) ^ 2 / (8 * θ * (1 + 2 * θ)) := by sorry

end BOGOPromo.NoStockpile
