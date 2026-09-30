-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_rebate_first_order_condition
-- name    : FalseFailureReturns.TargetRebate.rebate_first_order_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:40:46.121658+00:00
-- url     : https://prove2.me/theorems/410a999a-36e6-403f-b784-d6f882c5d66e
-- title:
--   §3.1, Eq. (9): first-order condition for the retailer's optimal effort under a target rebate
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ be as in the model, and let $(u, T)$ be a target rebate contract with $u > 0$ and $T > 0$, with $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Suppose an effort $\rho^* > 1$ maximizes the retailer's expected profit $\rho \mapsto \pi_R(\rho \mid T, u)$ over $\rho \ge 1$, and $T < 2\beta/\rho^*$. Then
--   $$T^2 u (\rho^*)^2 - 4a\beta(\rho^*)^3 + 4R_r\beta^2 = 0. \tag{9}$$
--
--   Equation (9) links $u$, $T$ and the induced effort; substituting $\rho^* = \rho^C$ gives the coordinating contracts (10) and all the profit identities of the appendix.
--
--   **Formalization Note** The paper's "the value $\rho^*$ that maximizes (8)" is formalized as a maximizer of the true profit (6) over $\rho \ge 1$; the hypotheses $\rho^* > 1$ (an interior maximizer) and $T < 2\beta/\rho^*$ (so that (8) is the profit near $\rho^*$) are the conditions under which the paper's first-order condition applies.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, §3.1, Eq. (9)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem rebate_first_order_condition (P : Params) (T u ρs : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hu : 0 < u) (hT : 0 < T) (hρs : 1 < ρs)
    (hmax : IsMaxOn (rebateRetailerProfit P T u) (Set.Ici 1) ρs)
    (hTlt : T < 2 * P.β / ρs) :
    T ^ 2 * u * ρs ^ 2 - 4 * P.a * P.β * ρs ^ 3 + 4 * P.Rr * P.β ^ 2 = 0 := by sorry

end FalseFailureReturns.TargetRebate
