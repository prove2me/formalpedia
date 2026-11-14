-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_backward_kolmogorov_of_generator_limit
-- name    : AppliedSDE.SarkkaSolin.backward_kolmogorov_of_generator_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:56:05.900032+00:00
-- url     : https://prove2.me/theorems/3ec9d717-af1c-4bfe-b89b-ee8a3b590167
-- title:
--   General time-inhomogeneous backward Kolmogorov equation from transition kernels
-- statement:
--   Original derived analytical bridge to Theorem 5.11 (printed pp. 68–69). A sufficiently smooth transition density p(s,y;t,x) obeys Chapman–Kolmogorov and a right short-time diffusion generator limit with state-time drift b(s,y) and variance a(s,y). Under the actual limit identity, its negative derivative with respect to starting time equals the diffusion generator in the starting-state variable. This retains full variable coefficients and distinguishes the local generator condition from the backward PDE conclusion. Existence of an SDE transition density and validity of its generator limit remain additional source obligations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   -\partial_s p(s,y;t,x)=b(s,y)\partial_yp+\frac12 a(s,y)\partial_y^2p
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 5.11, equation (5.44), variable-coefficient generator bridge, printed p. 68. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.backward_kolmogorov_of_generator_limit
    (b a : ℝ → ℝ → ℝ)
    (p : ℝ → ℝ → ℝ → ℝ → ℝ)
    (s y t x : ℝ) (hst : s < t)
    (hTime : DifferentiableAt ℝ (fun u : ℝ => p u y t x) s)
    (hCK : ∀ h : ℝ, 0 < h → s + h < t →
      ∫ z : ℝ, p s y (s + h) z * p (s + h) z t x =
        p s y t x)
    (hGenerator : Tendsto
      (fun h : ℝ =>
        ((∫ z : ℝ, p s y (s + h) z * p (s + h) z t x) -
          p (s + h) y t x) / h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (b s y * deriv (fun z : ℝ => p s z t x) y +
        a s y / 2 *
          deriv (fun z : ℝ => deriv (fun w : ℝ => p s w t x) z) y))) :
    -(deriv (fun u : ℝ => p u y t x) s) =
      b s y * deriv (fun z : ℝ => p s z t x) y +
        a s y / 2 * deriv
          (fun z : ℝ => deriv (fun w : ℝ => p s w t x) z) y := by
  sorry
