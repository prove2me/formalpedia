-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_lamperti_scalar_drift_correction
-- name    : AppliedSDE.SarkkaSolin.lamperti_scalar_drift_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:54:52.020683+00:00
-- url     : https://prove2.me/theorems/a86436f5-a6ad-4245-a422-891a202a6833
-- title:
--   Scalar Lamperti transform converts state-dependent diffusion to unit dispersion
-- statement:
--   Original derived from Chapter 7.1, equations (7.3)–(7.5), printed pp. 98–99. Let σ>0 be a twice continuously differentiable scalar dispersion and let g be a twice differentiable change of coordinates whose derivative is 1/σ. Then the Itô chain-rule generator acting on g has drift b/σ−(1/2)σ′ and its diffusion coefficient is g′σ=1. This is a source-faithful one-dimensional analytic transformation and a prerequisite for the full stochastic pathwise Lamperti theorem. No stochastic-process equivalence is claimed by this statement.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   g'(x)=\sigma(x)^{-1},\quad b_g(x)=\frac{b(x)}{\sigma(x)}-\frac12\sigma'(x)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 7.1, equations (7.3)–(7.5), Lamperti drift transformation, printed pp. 98–99. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators Topology

theorem AppliedSDE.SarkkaSolin.lamperti_scalar_drift_correction
    (b σ g : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ) (hg : ContDiff ℝ 2 g)
    (hσpos : ∀ x : ℝ, 0 < σ x)
    (hgderiv : ∀ x : ℝ, deriv g x = (σ x)⁻¹) :
    ∀ x : ℝ,
      (deriv g x) * σ x = 1 ∧
      (deriv g x) * b x +
        σ x ^ 2 / 2 * deriv (fun y : ℝ => deriv g y) x =
          b x / σ x - (1 / 2 : ℝ) * deriv σ x := by
  sorry
