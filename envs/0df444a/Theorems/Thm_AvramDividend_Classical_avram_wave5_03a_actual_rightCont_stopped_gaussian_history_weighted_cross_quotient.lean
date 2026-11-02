-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_cross_quotient
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_cross_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:53:26.958908+00:00
-- url     : https://prove2.me/theorems/113d2c1d-f91e-496a-8e0f-5d14a88f2a95
-- title:
--   Exact original stopped Gaussian exponential covariance factors from any stopped-history multiplier
-- statement:
--   For the actual original ν=0 spectrally negative Lévy source, any bounded right-continuous stopping time τ and any stopped-history measurable and globally measurable random H, the source stopped Gaussian exponential quotient cross covariance weighted by H factors exactly into E[H] times (exp(h σ² θη)-1)/(θη), for nonnegative θ,η including zero. This comes from canonically proved same-path stopped-history independence, original stopped source quotient MemLp2, and original exact two-parameter cross energy; it is an exact source-coupled quadratic-energy transport useful toward the Gaussian bracket without detached Brownian or assumed stochastic integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_cross_quotient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      ((Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
    (∫ ω, H ω ∂P) *
      ((Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η)) := by
  sorry
