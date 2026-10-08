-- Prove2me | Theorems.Thm_CachonCoord_MarketClearing_p54_monopolist_value
-- name    : CachonCoord.MarketClearing.p54_monopolist_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:34:04.965925+00:00
-- url     : https://prove2.me/theorems/ea8e36da-5136-4267-b540-8edea06c8d49
-- title:
--   §6.5.2, p. 54 — the monopolist's expected profit is Π° = (1 + θ)/8
-- statement:
--   Let $\theta>1$, $p_l(q)=(1-q)^+$ and $p_h(q)=(1-q/\theta)^+$. A monopolist with zero production cost orders a stock $Q$ and, after observing the equally likely demand state, sells $x_l\in[0,Q]$ units in the low state and $x_h\in[0,Q]$ in the high state. Then
--   $$
--   \Pi^o=\tfrac12p_l(\tfrac12)\tfrac12+\tfrac12p_h(\tfrac\theta2)\tfrac\theta2=\frac{1+\theta}8,
--   $$
--   the stock $\theta/2$ is large enough to sell $1/2$ and $\theta/2$, and $\Pi^o$ is the greatest expected profit $\tfrac12p_l(x_l)x_l+\tfrac12p_h(x_h)x_h$ over all feasible $(Q,x_l,x_h)$.
--
--   This is the benchmark the decentralized system is compared with.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.2, p. 54, the display Π° = … = (1 + θ)/8

import Mathlib
import Definitions.Def_CachonCoord_MarketClearing_Model

namespace CachonCoord.MarketClearing

/-- §6.5.2, p. 54: the monopolist's expected profit is
`Π° = (1/2)p_l(1/2)(1/2) + (1/2)p_h(θ/2)(θ/2) = (1 + θ)/8`, and this is the largest expected profit
she can obtain by ordering a stock and selling any part of it in each demand state; the stock
`θ/2`, selling `1/2` in the low state and `θ/2` in the high state, attains it. -/
theorem p54_monopolist_value (θ : ℝ) (hθ : 1 < θ) :
    (1 / 2) * pl (1 / 2) * (1 / 2) + (1 / 2) * ph θ (θ / 2) * (θ / 2) = (1 + θ) / 8 ∧
    (1 / 2 : ℝ) ≤ θ / 2 ∧
    IsGreatest (monopolyOutcomes θ) ((1 + θ) / 8) := by sorry

end CachonCoord.MarketClearing
