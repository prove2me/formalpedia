-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:54:09.281345+00:00
-- url     : https://prove2.me/theorems/3b8f471a-fcbd-4835-b339-46d13701ea9d
-- title:
--   Exact source Gaussian stopped conditional quadratic energy for every stopped-history weight
-- statement:
--   For the same original Levy path, right-continuous stopped filtration and arbitrary Gaussian sigma, with zero jump measure, every ambient- and stopped-history measurable real weight H satisfies E[H (X_(tau+h)-X_tau-hc)^2] = E[H] h sigma^2. This combines the already Proved stopped-history square factorization with original-source exact stopped variance; no Brownian copy or sigma positivity. Intended as the conditional quadratic-variation finite-cell coefficient to feed the discounted w'' controlled-chain-rule component, without claiming a full continuous semimartingale Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_square_factor

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
    (∫ ω, H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
