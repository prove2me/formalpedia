-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_original_residual_L1_of_components
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_original_residual_L1_of_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:41:30.139024+00:00
-- url     : https://prove2.me/theorems/2ba278da-ee63-48db-96a7-bf2a7c2ebcf2
-- title:
--   Reconstruct discounted original generator HJB L1 from physically controlled continuous jump and payoff terms
-- statement:
--   Exact original SpectrallyNegativeLevy generator identity at a finite observed stopped state: the discounted generator-minus-q payoff density is L1 if its actual sigma²/2 plus canonical c physical coefficient, source compensated negative-mark integral, and payoff contribution have separately derived discounted L1. This adds no assumption of generator L1; each explicit term is an independent checkable prerequisite. No endpoint HJB, compensator or stochastic martingale is asserted.
-- source:
--   Original source SpectrallyNegativeLevy.generator definition with source truncation -1<z<0; finite clock L1 algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_original_residual_L1_of_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) (R : T → ℝ) (clock : T → ℝ≥0)
    (w : ℝ → ℝ) (q : ℝ) (A : Set T)
    (hcont : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
          X.c * deriv w (R t)))) μ)
    (hjump : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (R t) z ∂X.ν))) μ)
    (hpay : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) * w (R t))) μ) :
    Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.generator w (R t) - q * w (R t)))) μ := by sorry
