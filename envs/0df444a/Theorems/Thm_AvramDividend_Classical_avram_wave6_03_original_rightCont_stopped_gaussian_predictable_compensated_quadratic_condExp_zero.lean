-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:03:30.533305+00:00
-- url     : https://prove2.me/theorems/b41e838b-ddb4-4fd9-8bef-9a62884b7c1f
-- title:
--   Original predictably weighted stopped Gaussian compensated quadratic increment has conditional mean zero
-- statement:
--   On the actual zero-jump Lévy source Ω with bounded rightCont stop, every stopped-history measurable integrable H whose H times the actual drift-centred source increment square is integrable gives a true conditionally centered compensated quadratic increment H*Y²-h*sigma²*H, given the physical stopped σ-algebra. This is the martingale-difference form of the Gaussian quadratic correction; it follows from the newly Proved exact conditional weighted variance, stopped-history measurability and Mathlib conditional linearity, without sigma positivity or any Brownian-only surrogate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHI : Integrable H P)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    P[(fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
      ((h : ℝ) * X.σ ^ 2) * H ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
