-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_retailer_gain_corner
-- name    : FalseFailureReturns.TargetRebate.retailer_gain_corner
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:44:28.992095+00:00
-- url     : https://prove2.me/theorems/410448a3-f10a-4cfa-9d38-9142b81e8408
-- title:
--   Appendix, Eq. (31): if $\rho^D = 1$, the retailer is better off
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ with $(M_m + R_r)\beta > a$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Let $(u, T)$ with $u > 0$, $T > 0$ and $T < 2\beta/\rho^C$ coordinate the supply chain, and suppose the decentralized effort is at the minimum, $\rho^D = 1$. Then the retailer's gain is nonnegative:
--   $$\Delta_R = \pi_R(\rho^C \mid T, u) - \pi_R(\rho^D) \ge 0.$$
--
--   This is the second of the two cases of the retailer half of Proposition 2.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, pp. 392–393, Appendix, Eq. (31)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem retailer_gain_corner (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u)
    (hD : decentrEffort P = 1) :
    0 ≤ rebateRetailerProfit P T u (coordEffort P) - retailerProfit P (decentrEffort P) := by sorry

end FalseFailureReturns.TargetRebate
