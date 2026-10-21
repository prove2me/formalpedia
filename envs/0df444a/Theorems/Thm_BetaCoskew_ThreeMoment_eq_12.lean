-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_eq_12
-- name    : BetaCoskew.ThreeMoment.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:38.323516+00:00
-- url     : https://prove2.me/theorems/4b196c9f-ef14-4165-9dbc-5c2674adaedf
-- title:
--   Appendix A, equation (12): risk-free return fixes the multiplier
-- statement:
--   Suppose the kernel has the first-order form $\tilde m=(\lambda^*)^{-1}w'(1-F_M(\tilde R_M))u'(\tilde R_M)$ almost surely with $\lambda^*>0$, and the risk-free asset is priced by $\mathbb E[\tilde m](1+r_f)=1$. If the stated expectations are integrable, then
--
--   $$
--   \lambda^*=(1+r_f)\mathbb E[w'(1-F_M(\tilde R_M))u'(\tilde R_M)],
--   \qquad \tilde m=m(\tilde R_M)\quad P\text{-a.s.}
--   $$
--
--   This normalizes the first-order kernel and yields equation (4).
--
--   **Formalization Note** Integrability is explicit so the real-valued expectations do not take Lean's default value for a nonintegrable function.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 34, Appendix A, equation (12) and following sentence

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory

/-- Appendix A, equation (12): risk-free pricing determines the multiplier. -/
theorem eq_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u w : ℝ → ℝ) (rf : ℝ)
    (mt RM : Ω → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hmt : Integrable mt P)
    (hg : Integrable (fun ω =>
      deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) P)
    (hrf : (∫ ω, mt ω ∂P) * (1 + rf) = 1)
    (hkernel : mt =ᵐ[P] fun ω => lam⁻¹ *
      (deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω))) :
    lam = (1 + rf) * kernelMean P u w RM ∧
      mt =ᵐ[P] fun ω => mFun P u w rf RM (RM ω) := by sorry

end BetaCoskew.ThreeMoment
