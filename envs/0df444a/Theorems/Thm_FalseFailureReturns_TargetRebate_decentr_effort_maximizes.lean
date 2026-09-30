-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_decentr_effort_maximizes
-- name    : FalseFailureReturns.TargetRebate.decentr_effort_maximizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:38:02.906909+00:00
-- url     : https://prove2.me/theorems/8c012e55-f0fd-4ef1-a526-11a2d29e5b28
-- title:
--   Eqs. (3)–(4): the retailer's no-contract profit is maximized at $\rho^D$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$ and $R_r > 0$ be as in the model. Without a contract the retailer's expected profit at effort $\rho$ is
--   $$\pi_R(\rho) = -\frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big).$$
--   Over the effort domain $\rho \ge 1$ it is maximized at
--   $$\rho^D = \max\Big\{\Big(\frac{R_r\beta}{a}\Big)^{1/3},\,1\Big\},$$
--   that is, $\pi_R(\rho) \le \pi_R(\rho^D)$ for every $\rho \ge 1$.
--
--   This identifies $\rho^D$ as the effort the retailer exerts in the absence of an incentive from the manufacturer, the benchmark of the paper's comparisons.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 382, §3, Eqs. (3)–(4)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model

namespace FalseFailureReturns.TargetRebate

theorem decentr_effort_maximizes (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) :
    IsMaxOn (retailerProfit P) (Set.Ici 1) (decentrEffort P) := by sorry

end FalseFailureReturns.TargetRebate
