-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_uniform_rebate_profit
-- name    : FalseFailureReturns.TargetRebate.uniform_rebate_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:40:13.069055+00:00
-- url     : https://prove2.me/theorems/4ca88383-b9e0-422b-adf4-180696d02d43
-- title:
--   §3.1, Eq. (8): uniform expected shortfall $T^2\rho/4\beta$ and the retailer's rebate profit
-- statement:
--   Let $\beta > 0$ and $\rho > 0$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. For a target $T$ with $0 \le T \le 2\beta/\rho$,
--   $$E_X\{[T - X(\rho)]^+\} = \int_0^T (T - x)\,\frac{\rho}{2\beta}\,dx = \frac{T^2\rho}{4\beta},$$
--   and consequently, for every rebate $u$, the retailer's expected profit (6) under the contract $(u, T)$ is
--   $$\pi_R(\rho \mid T, u) = \frac{T^2 u\rho}{4\beta} - \frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big). \tag{8}$$
--
--   This closed form is what the first-order condition (9) and the appendix computations work with.
--
--   **Formalization Note** The paper prints $E_X\{[T - X(\rho)]^+\} = u\int_0^T(T - x)(\rho/2\beta)\,dx = T^2u\rho/4\beta$, with a stray factor $u$; the expectation is $T^2\rho/4\beta$ and $u$ times it is $T^2u\rho/4\beta$, as stated here. The range $0 \le T \le 2\beta/\rho$ is where the closed form holds (the paper's requirement $T < 2\beta/\rho$ on p. 383).
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, §3.1, Eq. (8)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem uniform_rebate_profit (P : Params) (T u ρ : ℝ)
    (hβ : 0 < P.β) (hρ : 0 < ρ) (hT0 : 0 ≤ T) (hT : T ≤ 2 * P.β / ρ) :
    expShortfall P.β ρ T = T ^ 2 * ρ / (4 * P.β) ∧
      rebateRetailerProfit P T u ρ =
        T ^ 2 * u * ρ / (4 * P.β) - P.a * ρ ^ 2 / 2 + P.Rr * P.β * (1 - 1 / ρ) := by sorry

end FalseFailureReturns.TargetRebate
