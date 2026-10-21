-- Prove2me | Theorems.Thm_AccountingRules_Threshold_prior_mean_le_implies_cond_mean_le
-- name    : AccountingRules.Threshold.prior_mean_le_implies_cond_mean_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:49.455852+00:00
-- url     : https://prove2.me/theorems/7ef86990-933e-4233-8c80-d1918f47720b
-- title:
--   Appendix A.1, p. 10 — a low prior mean gives a low mean below M
-- statement:
--   If the prior mean satisfies $\mathbb E_P[\theta]\le M-B$, then its conditional mean below the liquidation value also satisfies
--   $$\mathbb E_P[\theta\mid\theta\le M]\le M-B.$$
--   This connects the appendix's Case 1 to its first-best threshold conclusion in Case 2.1.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 10 (PDF 11), Appendix A.1, closing paragraph

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, closing paragraph, p. 10: the low-prior-mean case enters Case 2.1. -/
theorem prior_mean_le_implies_cond_mean_le (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B)
    (hmean : (∫ θ, θ ∂P) ≤ M - B) :
    condMean P id (Iic M) ≤ M - B := by sorry

end AccountingRules.Threshold
