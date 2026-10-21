-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_eq_6_7
-- name    : BetaCoskew.ThreeMoment.eq_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:39.160258+00:00
-- url     : https://prove2.me/theorems/c3d998f5-772a-4f32-8a44-37fc06ec7e8f
-- title:
--   Theorem 2, equations (6)–(7): closed-form beta and coskewness premiums
-- statement:
--   Let $F_M$ be the CDF of the market total return, with nonnegative continuously differentiable density $f$, and suppose $F_M(1)$ is strictly between $0$ and $1$. Assume $u$ and $w$ are three times continuously differentiable near $1$ and $1-F_M(1)$, respectively, the risk-free total return is positive, and $K=\mathbb E[w'(1-F_M(\tilde R_M))u'(\tilde R_M)]$ is nonzero. For the closed-form premiums $A$ and $B$ defined in (6)–(7),
--
--   $$
--   A=-(1+r_f)m'(1),\qquad B=-(1+r_f)m''(1).
--   $$
--
--   This identifies the coefficients in the three-moment CAPM with derivatives of the pricing function.
--
--   **Formalization Note** The paper's formulas use third derivatives although Assumption 1 supplies only first derivatives; the additional local smoothness and interior-CDF hypotheses make those formulas meaningful. Nonzero $K$ follows from equilibrium in the goal theorem.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 11, Theorem 2, equations (6)–(7)

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory

/-- Theorem 2, equations (6)–(7): the closed-form premiums are the first and
second derivatives of the equilibrium pricing function at total return 1. -/
theorem eq_6_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u w : ℝ → ℝ) (rf : ℝ)
    (RM : Ω → ℝ) (f : ℝ → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_smooth : ContDiff ℝ 1 f)
    (hf_law : P.map RM = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hF0 : 0 < cdf (P.map RM) 1) (hF1 : cdf (P.map RM) 1 < 1)
    (hu3 : ContDiffAt ℝ 3 u 1)
    (hw3 : ContDiffAt ℝ 3 w (1 - cdf (P.map RM) 1))
    (hrf : 0 < 1 + rf) (hK : kernelMean P u w RM ≠ 0) :
    premA P u w RM f = -(1 + rf) * deriv (mFun P u w rf RM) 1 ∧
    premB P u w RM f = -(1 + rf) * iteratedDeriv 2 (mFun P u w rf RM) 1 := by sorry

end BetaCoskew.ThreeMoment
