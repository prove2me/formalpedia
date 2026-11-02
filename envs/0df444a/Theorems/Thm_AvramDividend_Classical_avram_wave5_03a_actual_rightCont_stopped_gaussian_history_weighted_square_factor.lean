-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:14:48.297224+00:00
-- url     : https://prove2.me/theorems/790cc6dc-72c6-4746-bdda-febd0d3fcbb2
-- title:
--   Original stopped Gaussian squared increment is independent of every stopped-history observable
-- statement:
--   For the original pure-Gaussian spectrally negative Levy source X with nu=0, a bounded stopping time of the source right-continuous filtration, and any stopped-history measurable and ambient measurable real H, the expectation of H times the true drift-centred stopped source increment squared factorises exactly as E[H] times E[(X_(tau+h)-X_tau-hc)^2]. This is the genuine same-path stopped Gaussian conditional second-moment independence interface for predictable L2 localisation. It uses the already Proved full stopped-future-path independent-of-history theorem and actual source MemLp 2, and does not introduce a Brownian copy or assume an Ito bracket. Sigma may be zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
    (∫ ω, H ω ∂P) *
      (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 ∂P) := by
  sorry
