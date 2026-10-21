-- Prove2me | Theorems.Thm_AccountingRules_Threshold_case_1_A2_implies_A1
-- name    : AccountingRules.Threshold.case_1_A2_implies_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:44.800825+00:00
-- url     : https://prove2.me/theorems/47e63941-727e-4eb9-bb0e-043dbd7387be
-- title:
--   Appendix A.1, Case 1 — (A.2) implies (A.1) when the prior mean is low
-- statement:
--   Suppose the prior mean obeys $\mathbb E_P[\theta]\le M-B$. For every measurable binary rule $m$ with values in $[0,1]$, the high-signal constraint (A.2) implies the low-signal constraint (A.1):
--   $$\int\theta m\,dP\ge(M-B)\int m\,dP\quad\Longrightarrow\quad\int\theta(1-m)\,dP\le(M-B)\int(1-m)\,dP.$$
--   This identifies the redundant constraint in the appendix's first case.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 9 (PDF 10), Appendix A.1, Case 1

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 1, p. 9: (A.2) makes (A.1) redundant. -/
theorem case_1_A2_implies_A1 (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hmean : (∫ θ, θ ∂P) ≤ M - B)
    (m : ℝ → ℝ) (hm : IsRule m) (hA2 : A2 P M B m) : A1 P M B m := by sorry

end AccountingRules.Threshold
