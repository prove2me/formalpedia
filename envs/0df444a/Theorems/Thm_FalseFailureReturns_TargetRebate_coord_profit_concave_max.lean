-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_coord_profit_concave_max
-- name    : FalseFailureReturns.TargetRebate.coord_profit_concave_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:37:07.616897+00:00
-- url     : https://prove2.me/theorems/76eae95f-fc0c-4489-8864-650b1af23fa9
-- title:
--   Eqs. (1)–(2): the coordinated profit is concave and maximized at $\rho^C$
-- statement:
--   Let $a > 0$ be the marginal effort cost, $\beta > 0$ the expected number of false failures at minimum effort, and $M_m > 0$, $R_r > 0$ the manufacturer's and retailer's profits of avoiding one false failure return. The coordinated supply chain's expected profit
--   $$\Pi(\rho) = (M_m + R_r)\,\beta\Big(1 - \frac{1}{\rho}\Big) - \frac{a\rho^2}{2}$$
--   is concave on $\rho > 0$, and it is maximized over $\rho > 0$ at the coordinated effort
--   $$\rho^C = \Big[\frac{M_m + R_r}{a}\,\beta\Big]^{1/3}.$$
--
--   This identifies $\rho^C$ as the effort level a coordinating contract has to induce.
--
--   **Formalization Note** Concavity and maximality are stated on the open half-line $\rho > 0$, where the formula is meaningful; the effort domain $\rho \ge 1$ of the paper is contained in it, and $\rho^C \ge 1$ in the interesting case (see the next milestone).
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 381, §3, Eqs. (1)–(2)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model

namespace FalseFailureReturns.TargetRebate

theorem coord_profit_concave_max (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) :
    ConcaveOn ℝ (Set.Ioi 0) (coordProfit P) ∧
      IsMaxOn (coordProfit P) (Set.Ioi 0) (coordEffort P) := by sorry

end FalseFailureReturns.TargetRebate
