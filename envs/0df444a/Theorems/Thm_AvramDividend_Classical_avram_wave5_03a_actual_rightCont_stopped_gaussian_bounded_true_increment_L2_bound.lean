-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:38:31.150308+00:00
-- url     : https://prove2.me/theorems/300f507b-8120-4e70-9d83-82d2f12b9d34
-- title:
--   Actual source stopped Gaussian drift-centred increment obeys bounded predictable multiplier L2 inequality
-- statement:
--   For the literal original zero-jump Gaussian Lévy source with bounded stopping in its original right-continuous filtration, any bounded strongly measurable (in particular predictable) weight H satisfies an exact expected-square comparison for the actual drift-centred increment, not an exponential approximation. This source-specific bound is the shortest missing step for localising the actual capped dividend gradient against genuine Gaussian increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
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
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
      K ^ 2 * (∫ ω, (Y ω) ^ 2 ∂P) := by
  sorry
