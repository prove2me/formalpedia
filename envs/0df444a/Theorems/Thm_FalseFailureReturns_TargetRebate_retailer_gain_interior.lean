-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_retailer_gain_interior
-- name    : FalseFailureReturns.TargetRebate.retailer_gain_interior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:43:59.58519+00:00
-- url     : https://prove2.me/theorems/7d44ba12-d977-479f-932d-c47556d8b8eb
-- title:
--   Appendix, Eq. (30): if $\rho^D > 1$, the retailer gains at least $\beta M_m/(2\rho^C) \ge 0$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ with $(M_m + R_r)\beta > a$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Let $(u, T)$ with $u > 0$, $T > 0$ and $T < 2\beta/\rho^C$ coordinate the supply chain, and suppose the decentralized effort is interior, $\rho^D > 1$. Then the retailer's gain $\Delta_R = \pi_R(\rho^C \mid T, u) - \pi_R(\rho^D)$ satisfies
--   $$\Delta_R \;\ge\; \frac{\beta M_m}{2\rho^C} \;\ge\; 0. \tag{30}$$
--
--   This is the first of the two cases of the retailer half of Proposition 2.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 392, Appendix, Eqs. (28)–(30)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem retailer_gain_interior (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u)
    (hD : 1 < decentrEffort P) :
    P.β * P.Mm / (2 * coordEffort P) ≤
        rebateRetailerProfit P T u (coordEffort P) - retailerProfit P (decentrEffort P) ∧
      0 ≤ P.β * P.Mm / (2 * coordEffort P) := by sorry

end FalseFailureReturns.TargetRebate
