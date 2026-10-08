-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p57_buyback_profit
-- name    : CachonCoord.MarketClearing.p57_buyback_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:53:51.345391+00:00
-- url     : https://prove2.me/theorems/65f86e2d-e3fb-431f-810c-2bec8939f0bd
-- title:
--   §6.5.2, p. 57 — with b = 1/2 the retailers' profit is q(3/4 − w − q/(2θ)), zero at q = θ/2 when w = 1/2
-- statement:
--   Let $\theta>1$ and let the supplier buy back unsold units at $b=1/2$, so that the retailers sell at most $1/2$ in the low state and $\theta/2$ in the high state. For a total order $1/2<q<\theta/2$ and any wholesale price $w$ the retailers' expected profit is
--   $$
--   \tfrac12\big(p_l(\tfrac12)\tfrac12+b(q-\tfrac12)\big)+\tfrac12\big(p_h(q)q\big)-qw=q\Big(\frac34-w-\frac q{2\theta}\Big),
--   $$
--   and with $w=1/2$ their profit at $q=\theta/2$ is zero.
--
--   This is the profit the supplier uses to pick the full-refund wholesale price.
--
--   **Formalization Note** The sales rule (sell $\min(q,1-b)$ and $\min(q,\theta(1-b))$) is the page's verbal equilibrium argument, built into the definition.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 57, the buy-back displays

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model
import Definitions.Def_CachonCoord_MarketClearing_Contracts

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 57: with a buy-back `b = 1/2` and a total order `1/2 < q < θ/2` the retailers' profit is
`(1/2)(p_l(1/2)(1/2) + b(q − 1/2)) + (1/2)(p_h(q)q) − qw = q(3/4 − w − q/(2θ))`; and with `w = 1/2`
their profit at `q = θ/2` is zero. -/
theorem p57_buyback_profit (θ : ℝ) (hθ : 1 < θ) :
    (∀ w q : ℝ, 1 / 2 < q → q < θ / 2 →
      bbRetailerProfit θ (1 / 2) w q =
          (1 / 2) * (pl (1 / 2) * (1 / 2) + (1 / 2) * (q - 1 / 2)) + (1 / 2) * (ph θ q * q) - q * w ∧
      bbRetailerProfit θ (1 / 2) w q = q * (3 / 4 - w - q / (2 * θ))) ∧
    bbRetailerProfit θ (1 / 2) (1 / 2) (θ / 2) = 0 := by sorry

end CachonCoord.MarketClearing
