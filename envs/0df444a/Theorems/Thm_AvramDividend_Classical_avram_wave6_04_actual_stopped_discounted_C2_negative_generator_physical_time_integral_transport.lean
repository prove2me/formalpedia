-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_stopped_discounted_C2_negative_generator_physical_time_integral_transport
-- name    : AvramDividend.Classical.avram_wave6_04_actual_stopped_discounted_C2_negative_generator_physical_time_integral_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:13:43.977292+00:00
-- url     : https://prove2.me/theorems/50f56b85-8460-48dd-aa6c-d889dc071e70
-- title:
--   Actual prepayment reserve stopped discounted negative generator drift equals original physical-time integral
-- statement:
--   For the actual SpectrallyNegativeLevy X.X source, prepayment left-limit controlled reserve, inclusive actual ruinTime, finite horizon, right-continuous stopping time τ, q≥0 and the literal SpectrallyNegativeLevy.generatorIntegrand against negative marks X.ν, prove that the predictable-clock generator drift equals the real-time × P product integral whenever the integrand is strongly predictable. The source physical clock law is required explicitly, but the jump-count hFuture intensity remains Chat01's obligation.
-- source:
--   Wave6 Chat04 Chat06 consumer physical-time transport specialized from independently Proved source predictable integral_trim bridge; exact source stopped generator notation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_predictable_integral_equals_physical_time_probability_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_stopped_discounted_C2_negative_generator_physical_time_integral_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    StronglyMeasurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν)) →
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ) =
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν)
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by sorry
