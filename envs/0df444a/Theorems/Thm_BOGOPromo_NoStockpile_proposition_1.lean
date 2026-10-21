-- Prove2me | Theorems.Thm_BOGOPromo_NoStockpile_proposition_1
-- name    : BOGOPromo.NoStockpile.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:23:32.297132+00:00
-- url     : https://prove2.me/theorems/0a487455-c237-4f30-a12f-b93712de3732
-- title:
--   Proposition 1, pp. 14–15 (PDF 14–15) — retailer's best response under BOGO-NSP: BOGO iff w ≤ θ
-- statement:
--   Let $0<\theta\le 1$ and let the retailer, facing wholesale price $w$, choose between a single price and a BOGO, with consumers maximizing utility.
--
--   1. If $0<w\le\theta$, the BOGO with
--   $$p_b=\frac{1+w}{2},\qquad p_g=\frac{\theta+w}{2}$$
--   is a best response, with profit $\dfrac{\theta(2+\theta-6w)+w^2(1+2\theta)}{4\theta}$; every best response has expected demand $\dfrac{3\theta-w-2\theta w}{2\theta}$; and for $w<\theta$ this BOGO is the only best response.
--   2. If $\theta<w\le 1$, the single price $p=\frac{1+w}{2}$ is a best response, with profit $\frac{(1-w)^2}{2}$, and every best response has expected demand $1-w$.
--
--   This is the retailer's stage of the BOGO game; the demand it determines is what the manufacturer optimizes in Proposition 2.
--
--   **Formalization Note** The page's "the retailer's best response is" Table 2 is read as: the Table 2 policy is a best response, every best response sells the Table 2 demand, and the best response is unique where it is (for $w<\theta$). At $w=\theta$ the BOGO of Table 2 sells no second unit and ties with the single price, with equal demand.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, pp. 14–15 (PDF 14–15), Proposition 1 and Table 2 (2nd and 3rd columns)

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model

namespace BOGOPromo.NoStockpile

theorem proposition_1 (θ w : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (0 < w → w ≤ θ →
      IsBestRespB θ w (.bogo ((1 + w) / 2) ((θ + w) / 2)) ∧
      (BPolicy.bogo ((1 + w) / 2) ((θ + w) / 2)).profit θ w =
        (θ * (2 + θ - 6 * w) + w ^ 2 * (1 + 2 * θ)) / (4 * θ) ∧
      (∀ π : BPolicy, IsBestRespB θ w π → π.demand θ = (3 * θ - w - 2 * θ * w) / (2 * θ)) ∧
      (w < θ → ∀ π : BPolicy, IsBestRespB θ w π → π = .bogo ((1 + w) / 2) ((θ + w) / 2))) ∧
    (θ < w → w ≤ 1 →
      IsBestRespB θ w (.single ((1 + w) / 2)) ∧
      (BPolicy.single ((1 + w) / 2)).profit θ w = (1 - w) ^ 2 / 2 ∧
      ∀ π : BPolicy, IsBestRespB θ w π → π.demand θ = 1 - w) := by sorry

end BOGOPromo.NoStockpile
