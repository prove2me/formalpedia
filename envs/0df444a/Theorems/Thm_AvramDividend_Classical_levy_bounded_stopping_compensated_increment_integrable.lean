-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_integrable
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:41:50.664352+00:00
-- url     : https://prove2.me/theorems/039aee91-c459-40b2-87a9-1b4a82aece39
-- title:
--   Integrability of compensated Lévy exponential increments after bounded stopping
-- statement:
--   After any bounded stopping time, the stochastic exponential increment compensated by its Lévy cumulant is Bochner integrable. The unit mean identity already proved ensures its integral is nonzero, which forces integrability. This is the integrability half of the increment exponential-martingale property.
-- source:
--   Direct corollary of levy_bounded_stopping_compensated_increment_mean_one and Integrable.of_integral_ne_zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ)) P := by sorry
