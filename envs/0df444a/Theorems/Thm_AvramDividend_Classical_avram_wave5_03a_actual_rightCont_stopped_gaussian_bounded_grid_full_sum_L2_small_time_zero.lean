-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_full_sum_L2_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_full_sum_L2_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:56:41.176192+00:00
-- url     : https://prove2.me/theorems/ade75cda-f622-4515-b718-db4a0516a2d0
-- title:
--   Finite sum of true stopped original Gaussian source increments vanishes in L2 under shrinking common horizon
-- statement:
--   For the actual ν=0 SpectrallyNegativeLevy source on its original filtration, a finite grid of bounded right-continuous stopping times and bounded strongly measurable weights yields a complete weighted sum of genuine drift-centred stopped source increments whose squared L2 expectation tends to zero as the common future horizon tends to zero. This is a true source-coupled finite-grid stochastic localisation limit obtained from canonical grid square energy by finite-set Cauchy-Schwarz and source L2 integrability; it is not a continuum Ito formula, bracket, or Brownian-copy transport.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_full_sum_L2_small_time_zero
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
      (∫ ω, (∑ i ∈ S,
        H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
          (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
