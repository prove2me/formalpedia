-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_coordinating_target_iff
-- name    : FalseFailureReturns.TargetRebate.coordinating_target_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:41:33.499442+00:00
-- url     : https://prove2.me/theorems/cf53ce4a-d95e-4ac7-b25f-8da42ad2ea13
-- title:
--   §3.1, Eq. (10): the coordinating target $T(u)$, admissible iff $u > m + \delta_m(w-c)$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$ with $(M_m + R_r)\beta > a$, and let $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. For a target rebate contract with $u > 0$ and $T > 0$ the following are equivalent:
--
--   1. $(u, T)$ coordinates the supply chain (the coordinated effort $\rho^C$ maximizes $\pi_R(\cdot \mid T, u)$ over $\rho \ge 1$) and satisfies $T < 2\beta/\rho^C$;
--   2. $T$ is given by
--   $$T = \frac{2\beta^{2/3}a^{1/3}M_m^{1/2}}{u^{1/2}(M_m + R_r)^{1/3}} \tag{10}$$
--   and $u > M_m = m + \delta_m(w - c)$.
--
--   In words: for each rebate $u$ there is exactly one admissible coordinating target, and it exists precisely when the rebate exceeds the manufacturer's own profit of avoiding a false failure return. In particular coordinating contracts with $T < 2\beta/\rho^C$ exist, so the hypotheses of Proposition 2 can be met.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, §3.1, Eq. (10)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem coordinating_target_iff (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T) :
    (Coordinates P T u ∧ T < 2 * P.β / coordEffort P) ↔
      (T = 2 * P.β ^ ((2 : ℝ) / 3) * P.a ^ ((1 : ℝ) / 3) * P.Mm ^ ((1 : ℝ) / 2) /
          (u ^ ((1 : ℝ) / 2) * (P.Mm + P.Rr) ^ ((1 : ℝ) / 3)) ∧
        P.Mm < u) := by sorry

end FalseFailureReturns.TargetRebate
