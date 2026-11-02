-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:03:19.495194+00:00
-- url     : https://prove2.me/theorems/ab5f60fe-7ae6-40e6-9ea2-3dd40a6e43d4
-- title:
--   Bounded genuine stopped Gaussian source-gradient increment is in physical L2
-- statement:
--   For the original spectrally negative Levy source with zero jump measure, bounded right-continuous stopping time, and strongly measurable bounded H, the true stopped drift-centred increment multiplied by H is MemLp 2 under the original P. This follows from the canonically Proved source stopped increment MemLp 2, strong measurability of H and a pointwise squared bound by K²Y². It supplies the exact physical L2 well-definedness interface for bounded predictable-gradient finite-grid stochastic sums, without any Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    MemLp (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) 2 P := by
  sorry
