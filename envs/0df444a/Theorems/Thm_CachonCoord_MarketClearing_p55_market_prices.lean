-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p55_market_prices
-- name    : CachonCoord.MarketClearing.p55_market_prices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:09.732303+00:00
-- url     : https://prove2.me/theorems/f61d1c19-6e6d-4c73-9746-02b31e5e9cae
-- title:
--   §6.5.2, p. 55 — at w*(θ) the retailers order θ/(1 + θ) or θ/2 and the market clearing prices are as displayed
-- statement:
--   Let $\theta>1$. At the wholesale price $w^*(\theta)$ a competitive total order $q$ exists, and every competitive order $q$ satisfies:
--   1. if $\theta\le3$: $q=q_1(w^*(\theta))=\frac\theta{1+\theta}$, $p_l(q)=\frac1{1+\theta}$, $p_h(q)=\frac\theta{1+\theta}$;
--   2. if $\theta>3$: $q=q_2(w^*(\theta))=\frac\theta2$, $p_l(q)=0$, $p_h(q)=\frac12$.
--
--   These prices show where the wholesale contract loses profit: the low-state price falls below the monopoly price $1/2$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 55, the four displays after 'So when θ ≤ 3 the retailers order'

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 55: at the wholesale price `w*(θ)` the competitive retailers order
`q₁(w*(θ)) = θ/(1 + θ)` when `θ ≤ 3`, with market clearing prices `1/(1 + θ)` and `θ/(1 + θ)`,
and `q₂(w*(θ)) = θ/2` when `θ > 3`, with market clearing prices `0` and `1/2`. -/
theorem p55_market_prices (θ : ℝ) (hθ : 1 < θ) :
    (∃ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q) ∧
    ∀ q : ℝ, IsCompetitiveOrder (retailerProfit θ (wStar θ)) q →
      (θ ≤ 3 → q = q1 θ (wStar θ) ∧ q1 θ (wStar θ) = θ / (1 + θ) ∧
        pl q = 1 / (1 + θ) ∧ ph θ q = θ / (1 + θ)) ∧
      (3 < θ → q = q2 θ (wStar θ) ∧ q2 θ (wStar θ) = θ / 2 ∧
        pl q = 0 ∧ ph θ q = 1 / 2) := by sorry

end CachonCoord.MarketClearing
