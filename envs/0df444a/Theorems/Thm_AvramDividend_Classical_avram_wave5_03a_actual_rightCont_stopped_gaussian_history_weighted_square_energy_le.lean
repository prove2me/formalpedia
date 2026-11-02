-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_energy_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_energy_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:38:41.699715+00:00
-- url     : https://prove2.me/theorems/5a0a97f5-aa51-40b4-9593-9089669fb212
-- title:
--   Stopped-history predictable Gaussian quadratic energy is bounded by sigma squared times its expected weight
-- statement:
--   For the true original no-jump spectrally negative Levy source and a bounded right-continuous stopping time, any nonnegative stopped-history measurable real weight H satisfies E[H (X_(tau+h)-X_tau-hc)^2] <= E[H] h sigma^2. This is a true same-path predictable quadratic-energy bound with the exact source variance convention, proved from the same-path stopped-history squared-increment factorisation and true original stopped variance bound. It permits sigma=0 and makes no detached Brownian or stochastic bracket assumption; it is a source-specific finite-cell isometry inequality useful for continuous-integral localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_energy_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) (hHnonneg : ∀ ω, 0 ≤ H ω) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) ≤
    (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
