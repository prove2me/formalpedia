-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:15:23.967745+00:00
-- url     : https://prove2.me/theorems/a25487ff-1ca9-49b6-8ddd-5aa0f942f764
-- title:
--   Original Gaussian source finite-grid predictable exponential difference quotient has expectation zero
-- statement:
--   Fix the actual original-filtration spectrally negative Levy process with ν=0, an arbitrary finite family of time cells and uniformly bounded original-filtration predictable real coefficients. For any θ≥0 the finite sum of coefficients times the cumulant-centred exponential increments divided by θ has expectation zero. Integrability comes directly from deterministic source Laplace compensation; centering comes from its source expectation-one theorem; the Proved finite-grid predictable-centering theorem transports these facts to real adapted coefficients. This is a genuinely stochastic, same-path simple-integral identity, not the continuous Gaussian stochastic integral or a full chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  sorry
