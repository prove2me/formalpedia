-- Prove2me | Theorems.Thm_AccountingRules_Threshold_lagrangian_threshold_maximizer
-- name    : AccountingRules.Threshold.lagrangian_threshold_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:44.174878+00:00
-- url     : https://prove2.me/theorems/8d8b241b-7fd7-4f08-a2ef-551579eab21f
-- title:
--   Appendix A.1, Case 1 — the Lagrangian is maximized by a threshold rule
-- statement:
--   Fix a nonnegative multiplier $\lambda$. Among all measurable binary rules $m(\theta)\in[0,1]$, the linear Lagrangian term
--   $$\int\left(\theta-M+\frac{\lambda B}{1+\lambda}\right)m(\theta)\,dP(\theta)$$
--   is maximized by $m_\lambda(\theta)=1$ when $\theta>M-\lambda B/(1+\lambda)$ and $0$ otherwise. This gives the threshold shape used in both cases of Appendix A.1.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, pp. 9–10 (PDF 10–11), Appendix A.1, Case 1 Lagrangian display and threshold rule

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- Appendix A.1, Case 1, pp. 9–10: a nonnegative multiplier gives a threshold maximizer. -/
theorem lagrangian_threshold_maximizer (P : Measure ℝ) (θlo θhi M B lam : ℝ)
    (hS : Standing P θlo θhi M B) (hlam : 0 ≤ lam) (m : ℝ → ℝ)
    (hm : IsRule m) :
    (∫ θ, (θ - M + lam / (1 + lam) * B) * m θ ∂P) ≤
      ∫ θ, (θ - M + lam / (1 + lam) * B) *
        (Ioi (M - lam / (1 + lam) * B)).indicator (fun _ => (1 : ℝ)) θ ∂P := by sorry

end AccountingRules.Threshold
