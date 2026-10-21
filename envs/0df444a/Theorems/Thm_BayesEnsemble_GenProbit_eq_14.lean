-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_eq_14
-- name    : BayesEnsemble.GenProbit.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:08.523541+00:00
-- url     : https://prove2.me/theorems/940cdf1a-0119-4d58-a545-5bc27f1bb330
-- title:
--   Equation (14), p. 28 — Gaussian-link integral as a convolution cdf
-- statement:
--   Fix expert $i$ and a possible value $t$ of $\alpha_i x_i$. The remaining linear predictor, conditional on $\alpha_i x_i=t$, has mean $m_i(t)=\theta_{-i}+b_{-i,i}b_{i,i}^{-1}(t-\theta_i)$ and variance $v_i$. The conditional event probability $P(y=1\mid \alpha_i x_i=t)$ equals the following integral. For the link cdf $F_{z_0}$,
--
--   $$
--   P(y=1\mid \alpha_i x_i=t)=\int_{\mathbb R}F_{z_0}(u+t)\,dN(m_i(t),v_i)(u)
--   =F_{z_0+\sqrt{v_i}x_0}\bigl(m_i(t)+t\bigr).
--   $$
--
--   This is the probability identity obtained from the integral and independent-sum calculation in equation (14). It converts the conditional expectation of the link function into the cdf used in Proposition 4.
--
--   **Formalization Note** The measure integral remains meaningful if $v_i=0$, whereas the paper's displayed density $1/\sqrt{v_i}$ is only meaningful for positive $v_i$. The integrand is bounded between zero and one, so it is integrable.
--
--   **Formalization Note** The conditional-probability equality is almost sure in the realized value of $\alpha_i x_i$; a conditional probability is defined only up to a null set.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 28, equation (14) and the following identification

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- Equation (14), p. 28: the conditional link integral and its cdf form. -/
theorem eq_14 {k : ℕ} (P : Params k) (hP : Standing P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (Y : Set Ω) (hY : MeasurableSet Y)
    (hglm : μ[Y.indicator (1 : Ω → ℝ) | MeasurableSpace.comap x inferInstance]
      =ᵐ[μ] fun ω => cdf P.nu (P.alpha0 + ∑ i, P.alpha i * x ω i))
    (i : Fin k) :
    (μ[Y.indicator (1 : Ω → ℝ) |
      MeasurableSpace.comap (fun ω => P.alpha i * x ω i) inferInstance]
      =ᵐ[μ] fun ω =>
        ∫ u, cdf P.nu (u + P.alpha i * x ω i) ∂
          (gaussianReal (mi P i (P.alpha i * x ω i)) (vi P i).toNNReal)) ∧
    (∀ᵐ ω ∂μ,
      (∫ u, cdf P.nu (u + P.alpha i * x ω i) ∂
          (gaussianReal (mi P i (P.alpha i * x ω i)) (vi P i).toNNReal)) =
        G P (vi P i) (mi P i (P.alpha i * x ω i) + P.alpha i * x ω i)) := by sorry

end BayesEnsemble.GenProbit
