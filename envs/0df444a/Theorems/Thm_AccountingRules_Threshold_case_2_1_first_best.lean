-- Prove2me | Theorems.Thm_AccountingRules_Threshold_case_2_1_first_best
-- name    : AccountingRules.Threshold.case_2_1_first_best
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:47.396225+00:00
-- url     : https://prove2.me/theorems/182e7d65-c879-4078-814c-eeea631fa01d
-- title:
--   Appendix A.1, Case 2.1 — the first-best threshold M
-- statement:
--   If $\mathbb E_P[\theta\mid\theta\le M]\le M-B$, then the binary rule $m^*(\theta)=1\{\theta>M\}$ satisfies both (A.1) and (A.2) and maximizes the regulator's binary objective over every measurable $[0,1]$-valued rule:
--   $$\int\theta m\,dP+M(1-\int m\,dP)\le\int\theta m^*\,dP+M(1-\int m^*\,dP).$$
--   It gives the paper's first-best case, where private continuation benefits do not distort the liquidation decision.
--
--   **Formalization Note** The conditional mean has a positive denominator under the standing full-support assumption.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 10 (PDF 11), Appendix A.1, Case 2.1

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 2.1, p. 10: the first-best threshold is M. -/
theorem case_2_1_first_best (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B)
    (hcond : condMean P id (Iic M) ≤ M - B) :
    let mstar : ℝ → ℝ := (Ioi M).indicator (fun _ => (1 : ℝ))
    A1 P M B mstar ∧ A2 P M B mstar ∧
      ∀ m : ℝ → ℝ, IsRule m → objective P M m ≤ objective P M mstar := by sorry

end AccountingRules.Threshold
