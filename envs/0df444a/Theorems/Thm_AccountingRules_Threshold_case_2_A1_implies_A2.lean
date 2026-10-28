-- Prove2me | Theorems.Thm_AccountingRules_Threshold_case_2_A1_implies_A2
-- name    : AccountingRules.Threshold.case_2_A1_implies_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:37.942987+00:00
-- url     : https://prove2.me/theorems/5bf0b143-dfe9-4c30-b310-9ff3bab8dc47
-- title:
--   Appendix A.1, Case 2 — (A.1) implies (A.2) when the prior mean is high
-- statement:
--   Suppose $\mathbb E_P[\theta]>M-B$. For every measurable binary rule $m$ with values in $[0,1]$, the low-signal constraint (A.1) implies the high-signal constraint (A.2):
--   $$\int\theta(1-m)\,dP\le(M-B)\int(1-m)\,dP\quad\Longrightarrow\quad\int\theta m\,dP\ge(M-B)\int m\,dP.$$
--   This identifies the redundant constraint in the appendix's second case.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 10 (PDF 11), Appendix A.1, Case 2

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 2, p. 10: (A.1) makes (A.2) redundant. -/
theorem case_2_A1_implies_A2 (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hmean : M - B < ∫ θ, θ ∂P)
    (m : ℝ → ℝ) (hm : IsRule m) (hA1 : A1 P M B m) : A2 P M B m := by sorry

end AccountingRules.Threshold
