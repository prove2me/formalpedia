-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:57:31.684734+00:00
-- url     : https://prove2.me/theorems/1dbe4390-8d45-4a6a-b770-a5ad21c1b8db
-- title:
--   Genuine stopped Gaussian simple integral is L2 and exactly mean-zero from stopped-history measurability alone
-- statement:
--   For the real original spectrally negative Lévy source with zero jump measure and bounded right-continuous stop τ, any real coefficient H measurable at its stopped history and uniformly bounded by nonnegative K has a genuine stopped drift-centred source stochastic-integral cell H·(X_(τ+h)-X_τ-hc) in L2(P) with exact expectation zero. Its stopped-history measurability automatically implies global measurability using the canonical stopped sigma-algebra inclusion, so no separate global measurability premise is imposed. This source-specific localisation directly imports both the Proved original stopped strong-Markov weighted mean-zero and the Proved original bounded-weight L2 result, and allows σ=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_simple_integral_L2_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω, |H ω| ≤ K) :
    MemLp (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P ∧
    (∫ ω, H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) = 0 := by
  sorry
