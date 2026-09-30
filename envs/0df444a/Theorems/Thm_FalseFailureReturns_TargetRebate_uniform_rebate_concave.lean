-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_uniform_rebate_concave
-- name    : FalseFailureReturns.TargetRebate.uniform_rebate_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:39:33.16072+00:00
-- url     : https://prove2.me/theorems/48ae31af-b8b9-4bca-ba97-6902c8bdfac5
-- title:
--   §3.1: with uniform $X(\rho)$ the retailer's rebate profit (6) is concave in $\rho$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ be as in the model, let $u \ge 0$ and let $T$ be any real target. Suppose the number of false failures at effort $\rho$ is $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Then the retailer's expected profit under the target rebate contract $(u, T)$,
--   $$\pi_R(\rho \mid T, u) = u\,E_X\{[T - X(\rho)]^+\} - \frac{a\rho^2}{2} + R_r\,\beta\Big(1 - \frac{1}{\rho}\Big),$$
--   is concave in $\rho$ on the effort domain $\rho \ge 1$.
--
--   This is the uniform instance of Proposition 1 that the paper invokes to make the first-order condition (9) sufficient.
--
--   **Formalization Note** The expectation is the true expectation under the uniform law for every $\rho$, including efforts with $2\beta/\rho < T$, where it no longer equals $T^2\rho/4\beta$.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, §3.1

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem uniform_rebate_concave (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr) (hu : 0 ≤ u) :
    ConcaveOn ℝ (Set.Ici 1) (rebateRetailerProfit P T u) := by sorry

end FalseFailureReturns.TargetRebate
