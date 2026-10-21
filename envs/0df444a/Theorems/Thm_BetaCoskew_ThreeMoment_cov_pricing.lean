-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_cov_pricing
-- name    : BetaCoskew.ThreeMoment.cov_pricing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:53.073984+00:00
-- url     : https://prove2.me/theorems/6a5a1e46-4510-4fb6-85a9-c0dcfeb092a2
-- title:
--   Appendix A, p. 35: covariance asset-pricing identity
-- statement:
--   Let $\tilde m$ be an integrable pricing kernel and $\tilde r_i$ an integrable asset return rate, with integrable product and $\mathbb E[\tilde m(1+\tilde r_i)]=1$. If $\mathbb E[\tilde m]>0$, then
--
--   $$
--   \operatorname{Cov}(\tilde m,1+\tilde r_i)
--     +\mathbb E[1+\tilde r_i]\mathbb E[\tilde m]=1,
--   \qquad
--   \mathbb E[\tilde r_i]
--     =\frac{1-\operatorname{Cov}(\tilde m,\tilde r_i)}{\mathbb E[\tilde m]}-1.
--   $$
--
--   The identity converts the asset pricing equation into expected return and covariance terms. It is the final algebraic step in Appendix A.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 34–35, Appendix A, covariance display on p. 35

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory

/-- Appendix A, p. 35: the covariance form of the asset pricing equation. -/
theorem cov_pricing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (mt ri : Ω → ℝ)
    (hmt : Integrable mt P) (hri : Integrable ri P)
    (hprod : Integrable (fun ω => mt ω * ri ω) P)
    (hprice : (∫ ω, mt ω * (1 + ri ω) ∂P) = 1)
    (hmean : 0 < ∫ ω, mt ω ∂P) :
    cov[mt, fun ω => 1 + ri ω; P] +
      (∫ ω, 1 + ri ω ∂P) * (∫ ω, mt ω ∂P) = 1 ∧
    (∫ ω, ri ω ∂P) =
      (1 - cov[mt, ri; P]) / (∫ ω, mt ω ∂P) - 1 := by sorry

end BetaCoskew.ThreeMoment
