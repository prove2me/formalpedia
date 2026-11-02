-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:38:52.691954+00:00
-- url     : https://prove2.me/theorems/63ff3d8c-07c7-40dc-9c70-8f7e000ed61d
-- title:
--   Original stopped-history Gaussian cell satisfies weighted L2 isometry upper bound
-- statement:
--   The original no-jump source Gaussian martingale-difference cell H (X_(tau+h)-X_tau-hc) has expected square bounded by h sigma^2 times the actual expected square of the stopped-history predictable coefficient H. Both time and gradient are genuine original-filtration quantities. Derive by applying the Proved original stopped Gaussian squared-increment independent-of-history factorisation to H^2 and the Proved original source stopped variance bound. This is the L2 isometry inequality suitable for constructing stochastic-integral limits, with exact source sigma variance convention and sigma=0 included. No detached Brownian, bracket equality, or full Ito formula is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_le
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
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) ≤
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
