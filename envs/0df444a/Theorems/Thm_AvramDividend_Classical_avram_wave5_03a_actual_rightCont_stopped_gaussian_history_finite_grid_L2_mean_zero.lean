-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:12:31.877898+00:00
-- url     : https://prove2.me/theorems/85a14eda-8364-4ba0-883d-2b6510fd21eb
-- title:
--   Genuine finite-grid stopped Gaussian stochastic integral is L2 and exactly centred
-- statement:
--   For the actual original no-jump spectrally negative Levy source and a finite family of bounded right-continuous stopping clocks with uniformly bounded stopped-history random weights, the genuine finite stochastic sum of drift-centred source increments is both in L2(P) and exactly mean-zero. Each source cell has proved original L2 membership; the finite sum is L2 by pinned Mathlib memLp_finset_sum and mean-zero by the already Proved original stopped-history finite-grid martingale difference theorem. No Brownian copy or artificial independence of overlapping cells. Sigma may be zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_L2_mean_zero
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
    MemLp (fun ω => ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)) 2 P ∧
    (∫ ω, ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
  sorry
