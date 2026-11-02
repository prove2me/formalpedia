-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:57:40.61495+00:00
-- url     : https://prove2.me/theorems/9a0312c4-b55e-423e-9e0b-28153d36ba60
-- title:
--   Original right-continuously stopped Gaussian source finite-grid integrals are exactly centred
-- statement:
--   On the original Lévy probability space, under ν=0 and with any finite family of distinct bounded right-continuous stopping clocks τ_i and coefficients H_i measurable at their own stopped histories, globally strongly measurable and bounded by K_i, the whole genuine finite stochastic sum Σ_i H_i·(X_(τ_i+h_i)−X_τ_i−h_i c) has expectation zero. Use the proved genuine source stopped-history orthogonality per cell and the proved bounded weighted source MemLp2 to justify integrable finite-sum interchange. No Gaussian positivity, detached Brownian, or artificial independence of overlapping cells is imposed; this is a source-specific stopped simple integral localisation interface, not continuous Ito or bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i : ι, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0)
    (H : ι → Ω → ℝ)
    (hHstopped : ∀ i : ι,
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ K i) :
    (∫ ω, ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
  sorry
