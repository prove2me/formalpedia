-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_ou_gp_single_observation_kalman
-- name    : AppliedSDE.SarkkaSolin.stationary_ou_gp_single_observation_kalman
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:45:50.413126+00:00
-- url     : https://prove2.me/theorems/dd8b41dc-f819-4d4c-bce2-4c06949b266a
-- title:
--   Stationary OU Gaussian-process observation agrees with a scalar Kalman update
-- statement:
--   Consider a scalar stationary Ornstein–Uhlenbeck prior with mean m0, mean-reversion rate λ>0 and diffusion variance q>0. Its stationary variance is V=q/(2λ). Represent that Gaussian prior as X=m0+sqrt(V)Z and a single noisy linear observation Y=hX+sqrt(r)E for independent standard Gaussians Z,E and observation variance r>0. Then the conditional expectation of X given Y is the Kalman/GP-regression posterior mean m0+Vh/(h²V+r)(Y-hm0), and the conditional squared-error variance is Vr/(h²V+r). This is a nontrivial single-observation bridge between the stationary SDE Gaussian model, the Kalman update, and Gaussian-process regression. It is staged as a capstone prerequisite; the full multi-time GP filtering and smoothing capstone still requires a stronger theorem.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   m_{\mathrm{post}}=m_0+\frac{Vh}{h^2V+r}(y-hm_0)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Example 5.7, Algorithm 10.9 and Section 12.4, printed pp. 65, 208 and 263–266. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.stationary_ou_gp_single_observation_kalman
    (rate q r : ℝ) (hrate : 0 < rate) (hq : 0 < q) (hr : 0 < r)
    (m₀ h : ℝ) :
    let V : ℝ := q / (2 * rate)
    let γ : Measure (ℝ × ℝ) :=
      (gaussianReal 0 1).prod (gaussianReal 0 1)
    let X : ℝ × ℝ → ℝ := fun z => m₀ + Real.sqrt V * z.1
    let Y : ℝ × ℝ → ℝ := fun z => h * X z + Real.sqrt r * z.2
    let gain : ℝ := V * h / (h ^ 2 * V + r)
    let post : ℝ × ℝ → ℝ := fun z => m₀ + gain * (Y z - h * m₀)
    (γ[X | MeasurableSpace.comap Y inferInstance] =ᵐ[γ] post) ∧
    (γ[(fun z => (X z - post z) ^ 2) |
      MeasurableSpace.comap Y inferInstance] =ᵐ[γ]
      fun _ => V * r / (h ^ 2 * V + r)) := by
  sorry
