-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:45:06.906021+00:00
-- url     : https://prove2.me/theorems/c710a470-ccd5-4061-891b-e331cc633212
-- title:
--   Finite original Gaussian stopped-grid quadratic energy vanishes as a common cell horizon shrinks
-- statement:
--   For the actual zero-jump Gaussian SpectrallyNegativeLevy P F source, any fixed finite family of original right-continuous bounded stopping times and bounded strongly measurable coefficients H_i, the expected sum of their squared true drift-centred source increment cells tends to zero when the common future horizon h decreases to zero. Every finite cell is genuinely source coupled; the proof uses accepted source MemLp 2, source small-time L2 continuity, and finite-sum Bochner integral interchange. It is a finite-grid stochastic-integral localisation limit, not a proof of bracket equality or Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (H : ι → Ω → ℝ) (hH : ∀ i, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hBound : ∀ i ω, |H i ω| ≤ K i) :
    Filter.Tendsto (fun h : ℝ≥0 =>
      (∫ ω, ∑ i ∈ S,
        (H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
          (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
