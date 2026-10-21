-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_eq_13
-- name    : BetaCoskew.ThreeMoment.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:40.572978+00:00
-- url     : https://prove2.me/theorems/e4d7b075-2018-4e43-b824-7d36554d025c
-- title:
--   Appendix A, equation (13): quadratic expansion of the pricing kernel
-- statement:
--   Let $F_M$ have a continuously differentiable density $f$, with $0<F_M(1)<1$, and let $u$ and $w$ have three continuous derivatives near the expansion points. For every positive multiplier $\lambda^*$, define $g(x)=(\lambda^*)^{-1}w'(1-F_M(1+x))u'(1+x)$. Equation (13) gives explicit coefficients $c_0,c_1,c_2$ in $w',w'',w'''$, $u',u'',u'''$, $f(1)$ and $f'(1)$ such that
--
--   $$
--   g(x)=c_0+c_1x+\frac{c_2}{2}x^2+o(x^2)\qquad(x\to0).
--   $$
--
--   The coefficients appear in full in the formal statement. This expansion supplies the market-return terms of the three-moment CAPM.
--
--   **Formalization Note** The little-o is a limit of real functions at zero, not an unconstrained random remainder.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 34, Appendix A, equation (13) and footnote 27

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

/-- Appendix A, equation (13): the pricing-kernel Taylor expansion at return 1,
with its explicit quadratic and little-o remainder. -/
theorem eq_13 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u w : ℝ → ℝ) (RM : Ω → ℝ)
    (f : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_smooth : ContDiff ℝ 1 f)
    (hf_law : P.map RM = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hF0 : 0 < cdf (P.map RM) 1) (hF1 : cdf (P.map RM) 1 < 1)
    (hu3 : ContDiffAt ℝ 3 u 1)
    (hw3 : ContDiffAt ℝ 3 w (1 - cdf (P.map RM) 1)) :
    let F := cdf (P.map RM)
    let p0 := 1 - F 1
    let c0 := lam⁻¹ * (deriv w p0 * deriv u 1)
    let c1 := lam⁻¹ *
      (deriv w p0 * iteratedDeriv 2 u 1 -
        iteratedDeriv 2 w p0 * deriv u 1 * f 1)
    let c2 := lam⁻¹ *
      (deriv w p0 * iteratedDeriv 3 u 1 -
        iteratedDeriv 2 w p0 *
          (2 * iteratedDeriv 2 u 1 * f 1 + deriv u 1 * deriv f 1) +
        iteratedDeriv 3 w p0 * deriv u 1 * f 1 ^ 2)
    (fun x : ℝ => lam⁻¹ * deriv w (1 - F (1 + x)) * deriv u (1 + x) -
      (c0 + c1 * x + c2 / 2 * x ^ 2)) =o[𝓝 0] (fun x : ℝ => x ^ 2) := by sorry

end BetaCoskew.ThreeMoment
