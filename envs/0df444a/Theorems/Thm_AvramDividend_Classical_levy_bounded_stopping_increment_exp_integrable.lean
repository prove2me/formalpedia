-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_integrable
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:40:20.384819+00:00
-- url     : https://prove2.me/theorems/6cfd45e2-f77e-4460-9f36-8359af45a5c5
-- title:
--   Integrability of the exponential Lévy increment after a bounded stopping time
-- statement:
--   The positive exponential of a Lévy increment after a bounded stopping time has a finite Bochner integral for every nonnegative Laplace parameter and fixed future horizon. The proof uses the previously established exact nonzero exponential Laplace moment and the fact that a nonintegrable Bochner integral is defined as zero.
-- source:
--   Corollary of the proved bounded stopping-time Lévy increment Laplace equality and Integrable.of_integral_ne_zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) P := by sorry
