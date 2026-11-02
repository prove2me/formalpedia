-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
-- name    : AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:11:03.461675+00:00
-- url     : https://prove2.me/theorems/89aa4b30-9d65-4819-b02a-38b8fd219f2a
-- title:
--   Actual stopped Gaussian source exponential difference quotient is L2 and exactly centred
-- statement:
--   For the actual original-filtration pure-Gaussian Levy source and any bounded stopping time, the centred exponential difference quotient has finite L2 energy and exactly zero expectation, for every nonnegative exponential parameter including zero. Both facts transport the Proved original source stopping-time exponential integrability and mean-one theorems, preserving the same source path and variance convention. This is an approximation to a Gaussian martingale increment; existence of the Brownian/continuous martingale representation and stochastic integral remain open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_centered_memLp_two

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) 2 P ∧
      (∫ ω, (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ ∂P) = 0 := by
  sorry
