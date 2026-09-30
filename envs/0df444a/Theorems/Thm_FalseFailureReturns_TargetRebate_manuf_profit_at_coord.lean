-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_manuf_profit_at_coord
-- name    : FalseFailureReturns.TargetRebate.manuf_profit_at_coord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:42:15.12809+00:00
-- url     : https://prove2.me/theorems/99bd54ae-d71f-4c33-b21f-05bd24ffa7ae
-- title:
--   Appendix, Eq. (25): the manufacturer's profit under a coordinating rebate is $M_m\beta(\rho^C-2)/\rho^C$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ with $(M_m + R_r)\beta > a$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Let $(u, T)$ with $u > 0$, $T > 0$ and $T < 2\beta/\rho^C$ coordinate the supply chain. Then the manufacturer's expected profit (7) at the coordinated effort is
--   $$\pi_M(\rho^C \mid T, u) = M_m\,\beta\,\frac{\rho^C - 2}{\rho^C}.$$
--
--   Comparing this with the no-contract profit $\pi_M(\rho^D) = M_m\beta(1 - 1/\rho^D)$ gives the manufacturer half of Proposition 2.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 392, Appendix, Eq. (25)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem manuf_profit_at_coord (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u) :
    rebateManufProfit P T u (coordEffort P) =
      P.Mm * P.β * ((coordEffort P - 2) / coordEffort P) := by sorry

end FalseFailureReturns.TargetRebate
