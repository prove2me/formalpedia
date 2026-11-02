-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:24:36.67586+00:00
-- url     : https://prove2.me/theorems/d72f6f5e-6d97-4db4-893f-66f0e49622d0
-- title:
--   Finite sums of genuine right-continuously stopped bounded-weight Gaussian source increments are L2
-- statement:
--   For the actual spectrally negative Levy process X with zero Levy jump measure, original right-continuous filtration and an arbitrary finite family of bounded stopping times, each bounded measurable random-weighted drift-centred stopped source increment is square integrable. Their finite sum is thus MemLp 2 under the original source probability. Each summand uses the real same-path X, not a Brownian surrogate. The result constructs the finite-grid square-integrability interface; it does not claim independence, zero mean or Brownian quadratic variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0)
    (H : ι → Ω → ℝ) (hH : ∀ i, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hBound : ∀ i ω, |H i ω| ≤ K i) :
    MemLp (fun ω => ∑ i ∈ S,
      H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)) 2 P := by
  sorry
