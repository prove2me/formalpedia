-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:12:21.240451+00:00
-- url     : https://prove2.me/theorems/fe784dd7-a525-4fae-a4cb-63cc9c0c48ca
-- title:
--   True original bounded-weight stopped Gaussian increment is L2-continuous at zero time
-- statement:
--   For the literal original ν=0 spectrally negative Gaussian Lévy source, a bounded stopping time in its right-continuous original filtration, and a bounded strongly measurable random weight, the real squared expectation of the weight times its genuine stopped drift-centred increment tends to zero as h→0 in ℝ≥0. This follows quantitatively from the canonically Proved same-source weighted real L2 bound and the exact hσ² variance convention, using a squeeze. It is a source-path and original-filtration small-time stochastic integration localisation interface; no Brownian copy or continuous Ito formula is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (H : Ω → ℝ) (hHmeas : StronglyMeasurable H)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ ω, |H ω| ≤ K) :
    Filter.Tendsto
      (fun h : ℝ≥0 =>
        (∫ ω, (H ω *
          (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
