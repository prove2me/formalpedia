-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
-- name    : AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:27:04.28926+00:00
-- url     : https://prove2.me/theorems/6c6f7684-1d83-4271-ac6d-3e584327e2e4
-- title:
--   Finite-horizon Esscher exponential tilt defines an actual probability measure
-- statement:
--   For every deterministic horizon and nonnegative Esscher parameter, weighting the spectrally negative Lévy law by its compensated exponential density exp(θX_t−tψ(θ)) defines a probability measure on the original measurable sample space. This is the exact finite-horizon Esscher law, constructed without a global extension or assuming the two-sided exit identity.
-- source:
--   Use Proved esscher_exp_process_integrable and levy_compensated_exponential_expectation_one. The exponential density is nonnegative, so Mathlib ofReal_integral_eq_lintegral_ofReal identifies its ENNReal mass with one; `withDensity_apply` gives measure_univ=1. This is the fundamental construction for proving that finite-horizon Esscher survival masses are genuine CDFs of the reflected running infimum and can be assembled via the Stieltjes machinery.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) := by sorry
