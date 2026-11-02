-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:41:46.160768+00:00
-- url     : https://prove2.me/theorems/b60fe94d-4b52-4e9d-9303-4ef2c50a5a5c
-- title:
--   Genuine stopped Gaussian source increment is orthogonal to every stopped-history observable
-- statement:
--   For an actual original SpectrallyNegativeLevy X with jump measure zero and any bounded right-continuous stopping time τ, every real-valued stopped-history measurable H also globally measurable has zero expectation when multiplied by the original drift-centred future Gaussian increment X_(τ+h)-X_τ-hc. Prove using same-path right-continuous stopped sigma-algebra independence, exact true stopped increment L2 and its separately proved original stopped mean zero. This gives the true source stopped simple stochastic-integral martingale-difference interface with no detached Brownian and with σ=0 allowed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
       (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) = 0 := by
  sorry
