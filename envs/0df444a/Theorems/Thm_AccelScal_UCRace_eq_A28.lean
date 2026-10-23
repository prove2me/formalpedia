-- Prove2me | Theorems.Thm_AccelScal_UCRace_eq_A28
-- name    : AccelScal.UCRace.eq_A28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:01.659694+00:00
-- url     : https://prove2.me/theorems/0a3f23c9-2e8f-4235-a0a5-b651d15aa227
-- title:
--   (A.27)–(A.28), p. 21 — strict log-supermodularity identity for Firm 1
-- statement:
--   For positive investment intensities $R_1,R_2$ and discount rate $r$, let $V_1$ be Firm 1's closed-form value from (9). The cross-partial expression used to test log-supermodularity satisfies
--
--   $$
--   V_1\frac{\partial^2 V_1}{\partial R_1\partial R_2}
--      -\frac{\partial V_1}{\partial R_1}\frac{\partial V_1}{\partial R_2}
--   =\frac{\partial\lambda_2}{\partial R_2}
--     \frac{(u_1\lambda_1-R_1)^2}{(r+\lambda_1+\lambda_2)^4}
--     \lambda'_1.
--   $$
--
--   The expression is strictly positive when both firms' discovery rates rise with their investment intensities and Firm 1's project surplus $u_1\lambda_1-R_1$ is nonzero. This is the paper's strict log-supermodularity calculation for the race.
--
--   **Formalization Note** Under the power-form technology, the derivative conditions correspond to $\gamma_1,\gamma_2>0$. The nonzero-surplus hypothesis is necessary for strictness: the squared factor vanishes at $R_1=\bar R_1$. The identity itself holds without that extra condition.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, Appendix A.6, p. 21, (A.27)–(A.28)

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section

namespace AccelScal.UCRace

/-- Lin, Appendix A.6, equations (A.27)–(A.28), p. 21. The strict
inequality requires a nonzero project surplus; it fails at the upper endpoint. -/
theorem eq_A28 (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    (let V := V1 T1 T2 r
     let lhs := V R1 R2 * deriv (fun b => deriv (fun a => V a b) R1) R2
       - deriv (fun a => V a R2) R1 * deriv (fun b => V R1 b) R2
     lhs = deriv T2.lam R2 * (T1.u R1 * T1.lam R1 - R1) ^ 2 /
         (r + T1.lam R1 + T2.lam R2) ^ 4 * deriv T1.lam R1 ∧
       (0 < T1.γ → 0 < T2.γ → T1.u R1 * T1.lam R1 ≠ R1 → 0 < lhs)) := by sorry

end AccelScal.UCRace
