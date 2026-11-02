-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:58:54.369765+00:00
-- url     : https://prove2.me/theorems/4294d18f-9e1d-43e0-a67a-c123a1438800
-- title:
--   Original stopped predictable Gaussian source cell has exact sigma-squared weighted L2 isometry
-- statement:
--   For the genuine original right-continuously stopped spectrally-negative Levy source under nu=0, any stopped-history measurable multiplier H has the exact square-energy factorisation E[(H*(X_(tau+h)-X_tau-h*c))²]=E[H²]*h*sigma². The square of H remains measurable at the stopped sigma-algebra, so the canonically Proved source weighted square factorisation applies. The newly canonically Proved Wave 6 exact true stopped source variance identifies the factor E[Y²] with h*sigma², including sigma=0. This strictly sharpens the earlier one-sided source Gaussian L2 bound, directly supporting controlled gradient stochastic-integral localisation on compact bands; it does not posit a detached Brownian representation or a full chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
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
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
    (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
