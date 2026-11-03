-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_stopped_discounted_negative_generator_ae_physical_time_integral_transport
-- name    : AvramDividend.Classical.avram_wave6_04_actual_stopped_discounted_negative_generator_ae_physical_time_integral_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:19:00.213305+00:00
-- url     : https://prove2.me/theorems/f5f4db91-375e-4518-a51d-27b4414e08cd
-- title:
--   Actual source stopped discounted negative generator drift: AE predictable physical-time integral transport
-- statement:
--   For the actual source X.X prepayment reserve, original inclusive ruinTime, right-continuous stopping time, discounted generator integrand over negative source Lévy marks X.ν and finite source physical clock, prove that the stopped generator drift integral equals the ordinary physical-time × source probability integral assuming only AEStronglyMeasurable with respect to μ. This is a stronger Chat06 consumer interface than the strongly measurable variant and does not establish the Chat01 jump intensity.
-- source:
--   Wave6 Chat04 specialization of Proved source AE predictable physical clock integral transport to exact stopped discounted generator expression.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_ae_predictable_integral_equals_physical_time_probability_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_stopped_discounted_negative_generator_ae_physical_time_integral_transport
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
    AEStronglyMeasurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν)) μ →
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ) =
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν)
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by sorry
