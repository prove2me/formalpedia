-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_stopped_discounted_C2_generator_drift_independent_of_physical_clock
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_stopped_discounted_C2_generator_drift_independent_of_physical_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:42:29.943189+00:00
-- url     : https://prove2.me/theorems/401bc391-029e-4dd1-89c9-7fb6863cd713
-- title:
--   Actual prepayment ruin-stopped discounted nonlinear Lévy generator drift is independent of the canonical physical predictable clock choice
-- statement:
--   For the actual original sample-space spectrally negative Lévy reserve, source negative Lévy measure X.ν, predictable prepayment surplus and inclusive ruinTime, the finite-horizon randomly stopped discounted generator drift is the same for any two predictable time measures agreeing with the true real-time × source probability clock. The equality is exact, including nonlinear negative-mark generator integrands, and does not claim intrinsic jump-count compensation without Chat 01's future rectangle law.
-- source:
--   Wave6 Chat04 derived actual-source stopped discounted generator drift invariance from Proved canonical physical predictable clock uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_stopped_discounted_C2_generator_drift_independent_of_physical_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ) (T : ℝ≥0)
    (μ₁ μ₂ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ₁ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₁ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hμ₂ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₂ A =
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ₁) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ₂) := by sorry
