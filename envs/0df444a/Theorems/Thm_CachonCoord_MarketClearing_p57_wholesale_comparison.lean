-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p57_wholesale_comparison
-- name    : CachonCoord.MarketClearing.p57_wholesale_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:43:22.227111+00:00
-- url     : https://prove2.me/theorems/274f1355-032e-4843-9c45-4849c8c28ece
-- title:
--   §6.5.2, p. 57 — the buy-back wholesale price exceeds the RPM one: 1/2 > (1 + θ)/(4θ)
-- statement:
--   For $\theta>1$,
--   $$
--   \frac12>\frac{1+\theta}{4\theta}.
--   $$
--   The buy-back contract's wholesale price $1/2$ exceeds resale price maintenance's $\bar w$, because with a buy-back retailers do not bear the cost of excess inventory in the low state.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 57, 'i.e., 1/2 > (1 + θ)/4θ'

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 57: the buy-back wholesale price exceeds the resale-price-maintenance one,
`1/2 > (1 + θ)/(4θ)`. -/
theorem p57_wholesale_comparison (θ : ℝ) (hθ : 1 < θ) :
    (1 + θ) / (4 * θ) < 1 / 2 := by sorry

end CachonCoord.MarketClearing
