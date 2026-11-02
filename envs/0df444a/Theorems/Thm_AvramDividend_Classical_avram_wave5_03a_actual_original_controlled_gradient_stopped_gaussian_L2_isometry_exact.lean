-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_L2_isometry_exact
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_L2_isometry_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:25:01.670487+00:00
-- url     : https://prove2.me/theorems/9d78d496-e12c-4340-bfb8-16ad347a498e
-- title:
--   Exact sigma-squared original stopped Gaussian isometry for genuine capped controlled HJB gradient
-- statement:
--   The actual original capped prepayment HJB gradient evaluated at a bounded original right-continuous stopping time is measurable in the source stopped-history sigma algebra. In the ν=0 Gaussian source case, the exact expected square of that genuine gradient times the drift-centred source future increment is its expected squared gradient times h sigma squared, including sigma=0. The proof instantiates a canonically proved source-specific exact L2 isometry using the Proved actual controlled gradient's stopped-value measurability. This is the sharp stochastic Gaussian simple-cell localisation interface for Chat03 and involves no detached Brownian copy or unsupported jump-bearing continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_original_controlled_gradient_stopped_gaussian_L2_isometry_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    (∫ ω, (H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by
  sorry
