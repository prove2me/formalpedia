-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_retailer_profit_at_coord
-- name    : FalseFailureReturns.TargetRebate.retailer_profit_at_coord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:42:46.388604+00:00
-- url     : https://prove2.me/theorems/df999e85-45e8-4856-8555-901bb549f32a
-- title:
--   Appendix, Eq. (27): the retailer's profit under a coordinating rebate
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ with $(M_m + R_r)\beta > a$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Let $(u, T)$ with $u > 0$, $T > 0$ and $T < 2\beta/\rho^C$ coordinate the supply chain. Then the retailer's expected profit (6) at the coordinated effort is
--   $$\pi_R(\rho^C \mid T, u) = \frac{\beta\,(M_m - 3R_r)}{2\rho^C} + R_r\,\beta. \tag{27}$$
--
--   The appendix compares this value with the retailer's no-contract profit $\pi_R(\rho^D)$ in the two cases $\rho^D > 1$ and $\rho^D = 1$.
--
--   **Formalization Note** The page writes $\pi_R(\rho \mid T, u)$ on the left of (26)–(27); the identity is at $\rho = \rho^C$, as stated here.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 392, Appendix, Eqs. (26)–(27)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem retailer_profit_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u) :
    rebateRetailerProfit P T u (coordEffort P) =
      P.β * (P.Mm - 3 * P.Rr) / (2 * coordEffort P) + P.Rr * P.β := by sorry

end FalseFailureReturns.TargetRebate
