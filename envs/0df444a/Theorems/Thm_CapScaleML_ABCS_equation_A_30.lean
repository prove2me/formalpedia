-- Prove2me | Theorems.Thm_CapScaleML_ABCS_equation_A_30
-- name    : CapScaleML.ABCS.equation_A_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:27.297659+00:00
-- url     : https://prove2.me/theorems/3d4fd7bd-74fd-45ea-857a-4fd153a13757
-- title:
--   Equation (A.30) — AP decomposition bound
-- statement:
--   Let $m_1$ be a feasible schedule under the predicted arrivals and let $m=m_1+m_2$, with $m_2$ AP's online correction for $\Delta\lambda=(\lambda-\tilde\lambda)^+$. Then
--   $$
--   \operatorname{Cost}^{\lambda}(m,T)\leq
--   \operatorname{Cost}^{\tilde\lambda}(m_1,T)
--   +(\sqrt{2\omega\beta}+\theta)T\|\Delta\lambda\|_{\mathrm{MAE}}.
--   $$
--   The appendix applies this bound in both directions when comparing actual and predicted optima.
--
--   **Formalization Note** The paper's use with the arrival rates swapped requires the formulation for any feasible $m_1$, rather than only an optimizer of the predicted problem.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 35, proof of Theorem 4.7, (A.30)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Equation (A.30), also used in the paper with the two arrival rates swapped. -/
theorem equation_A_30 (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat m₁ q₁ q : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hm₁ : Admissible T m₁) (hq₁ : IsWorkload T lamHat m₁ q₁)
    (hq : IsWorkload T lam (fun t => m₁ t + apOnline ω β lam lamHat t) q) :
    cost ω β θ T (fun t => m₁ t + apOnline ω β lam lamHat t) q ≤
      cost ω β θ T m₁ q₁ +
        ENNReal.ofReal ((Real.sqrt (2 * ω * β) + θ) *
          (T * mae T (deltaLam lam lamHat) (fun _ => 0))) := by sorry

end CapScaleML.ABCS
