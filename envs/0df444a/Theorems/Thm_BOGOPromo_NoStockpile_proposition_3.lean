-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_proposition_3
-- name    : BOGOPromo.NoStockpile.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:33.82493+00:00
-- url     : https://prove2.me/theorems/30f21a29-af0b-45da-bc9f-f3ccd784323c
-- title:
--   Proposition 3, p. 20 (PDF 20) — retailer's best response under PR-NSP: PR iff θ > 1/3 and w ≤ θ̄
-- statement:
--   Let $0<\theta\le 1$, $\bar\theta=\theta-(1-\theta)\sqrt{\theta/(1+\theta)}$, and let the retailer, facing wholesale price $w$, choose between a single price and a price reduction, with consumers maximizing utility.
--
--   1. If $1/3<\theta$ and $0<w\le\bar\theta$, the price reduction with
--   $$p_r=\frac{1+w}{2},\qquad p_d=\frac{2\theta+w+\theta w}{2(1+\theta)}$$
--   is a best response, with profit $\dfrac{\theta(1+5\theta)-6\theta w(1+\theta)+w^2(1+3\theta+2\theta^2)}{4\theta(1+\theta)}$, and for $w<\bar\theta$ it is the only best response.
--   2. If $\theta\le 1/3$ or $w>\bar\theta$, and $0<w\le 1$, the single price $p=\frac{1+w}{2}$ is a best response, with profit $\frac{(1-w)^2}{2}$, and every best response has expected demand $1-w$.
--
--   This is the retailer's stage of the PR game, used by the manufacturer in Proposition 4.
--
--   **Formalization Note** The page's part a) is stated for $1/3<\theta<1$ and part b) for $\theta\le 1/3$ or $w>\bar\theta$, which leaves $\theta=1$ (where $\bar\theta=1$) uncovered; part 1 here includes $\theta=1$, where the Table 2 policy ($p_d=p_r$) is optimal, because Proposition 4 and Corollary 4 use it. At $w=\bar\theta$ the retailer is indifferent between the price reduction and the single price, whose demands differ, so no common demand is claimed there.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, p. 20 (PDF 20), Proposition 3 and Table 2 (2nd and 4th columns)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem proposition_3 (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 / 3 < θ → 0 < w → w ≤ thetaBar θ →
      IsBestRespP θ w (.priceRed ((1 + w) / 2) ((2 * θ + w + θ * w) / (2 * (1 + θ)))) ∧
      (PPolicy.priceRed ((1 + w) / 2) ((2 * θ + w + θ * w) / (2 * (1 + θ)))).profit θ w =
        (θ * (1 + 5 * θ) - 6 * θ * w * (1 + θ) + w ^ 2 * (1 + 3 * θ + 2 * θ ^ 2)) /
          (4 * θ * (1 + θ)) ∧
      (w < thetaBar θ → ∀ π : PPolicy, IsBestRespP θ w π →
        π = .priceRed ((1 + w) / 2) ((2 * θ + w + θ * w) / (2 * (1 + θ))))) ∧
    ((θ ≤ 1 / 3 ∨ thetaBar θ < w) → 0 < w → w ≤ 1 →
      IsBestRespP θ w (.single ((1 + w) / 2)) ∧
      (PPolicy.single ((1 + w) / 2)).profit θ w = (1 - w) ^ 2 / 2 ∧
      ∀ π : PPolicy, IsBestRespP θ w π → π.demand θ = 1 - w) := by sorry

end BOGOPromo.NoStockpile
