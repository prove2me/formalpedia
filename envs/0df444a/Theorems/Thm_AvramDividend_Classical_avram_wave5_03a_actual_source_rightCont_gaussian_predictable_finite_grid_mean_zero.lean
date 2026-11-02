-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:21:23.635106+00:00
-- url     : https://prove2.me/theorems/4771c871-7193-4b13-a20c-d7485d584f6a
-- title:
--   Same original Lévy source right-continuous predictable Gaussian finite grids have zero expectation
-- statement:
--   For the actual spectrally negative Levy process X in its original probability space with ν=0, any finite grid and bounded coefficients adapted to the right-continuous filtration F.rightCont at the left endpoint have a centred cumulant-compensated Gaussian exponential quotient stochastic sum. This explicitly transports along the canonically Proved original-source right-continuous Levy lift with literally identical sample paths, drift, sigma and jump measure. No independent copy is introduced. This brings the simple stochastic-integral mean-zero interface into the same right-continuous predictable filtration as the corrected capped controlled gradient. The Brownian stochastic integral and bracket remain unconstructed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_finite_grid_predictable_exponential_quotient_integral_zero

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  sorry
