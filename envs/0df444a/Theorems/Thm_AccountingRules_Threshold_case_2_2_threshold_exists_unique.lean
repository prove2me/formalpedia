-- Prove2me | Theorems.Thm_AccountingRules_Threshold_case_2_2_threshold_exists_unique
-- name    : AccountingRules.Threshold.case_2_2_threshold_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:50.596625+00:00
-- url     : https://prove2.me/theorems/87adf0eb-8723-495b-96a6-53682a7a09e3
-- title:
--   Appendix A.1, Case 2.2 — unique interior conditional-mean threshold
-- statement:
--   Suppose $\underline\theta<M-B$ and $\mathbb E_P[\theta\mid\theta\le M]>M-B$. There is exactly one $\hat\theta\in(M-B,M)$ with
--   $$\mathbb E_P[\theta\mid\theta\le\hat\theta]=M-B.$$
--   This is the threshold equation (6) in the distorted liquidation case.
--
--   **Formalization Note** The strict lower-support hypothesis corrects Proposition 2's weak endpoint: at $\underline\theta=M-B$ an interior root need not exist. The conditional means here are only taken over positive-probability events.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, p. 10 (PDF 11), Appendix A.1, Case 2.2; p. 13 (PDF 14), endnote 11

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 2.2, p. 10: the conditional-mean equation has one interior root. -/
theorem case_2_2_threshold_exists_unique (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hlo : θlo < M - B)
    (hcond : M - B < condMean P id (Iic M)) :
    ∃! t : ℝ, t ∈ Ioo (M - B) M ∧ condMean P id (Iic t) = M - B := by sorry

end AccountingRules.Threshold
