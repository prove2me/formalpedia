-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p56_rpm_profit
-- name    : CachonCoord.MarketClearing.p56_rpm_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:46:22.365014+00:00
-- url     : https://prove2.me/theorems/95da1b12-824a-43b8-8609-225a707024b3
-- title:
--   §6.5.2, p. 56 — under resale price maintenance at p̄ = 1/2 with total stock θ/2, π_r(t) = q(t)((1 + θ)/(4θ) − w)
-- statement:
--   Let $\theta>1$ and impose resale price maintenance at $\bar p=1/2$ with proportional allocation. If the retailers' total stock is $\theta/2$, a retailer holding $q(t)$ units at wholesale price $w$ earns
--   $$
--   \pi_r(t)=-q(t)w+\frac12\Big(\frac{1/2}{\theta/2}q(t)\Big)\bar p+\frac12q(t)\bar p=q(t)\Big(\frac{1+\theta}{4\theta}-w\Big),
--   $$
--   and, for $q(t)>0$, $\pi_r(t)=0$ exactly when $w=\bar w=\frac{1+\theta}{4\theta}$.
--
--   This determines the wholesale price the supplier can charge with resale price maintenance.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 56, the displays π_r(t) and w̄ following Eq. (23)

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 56: under resale price maintenance with `p̄ = 1/2` and total stock `θ/2`, a retailer
holding `q(t)` units earns `π_r(t) = −q(t)w + (1/2)(((1/2)/(θ/2))q(t))p̄ + (1/2)q(t)p̄
= q(t)((1 + θ)/(4θ) − w)`, which (for `q(t) > 0`) is zero exactly at `w̄ = (1 + θ)/(4θ)`. -/
theorem p56_rpm_profit (θ w y : ℝ) (hθ : 1 < θ) :
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y =
      -y * w + (1 / 2) * (((1 / 2) / (θ / 2)) * y) * (1 / 2) + (1 / 2) * y * (1 / 2) ∧
    rpmRetailerProfit θ (1 / 2) w (θ / 2) y = y * ((1 + θ) / (4 * θ) - w) ∧
    (0 < y → (rpmRetailerProfit θ (1 / 2) w (θ / 2) y = 0 ↔ w = (1 + θ) / (4 * θ))) := by sorry

end CachonCoord.MarketClearing
