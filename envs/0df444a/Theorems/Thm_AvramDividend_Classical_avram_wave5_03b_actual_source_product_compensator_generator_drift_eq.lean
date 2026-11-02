-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:36:38.352921+00:00
-- url     : https://prove2.me/theorems/c4008b6d-97ae-499b-91fb-bcda5c608340
-- title:
--   Actual ruin-stopped original negative source product compensator equals nonlinear generator drift with integrability
-- statement:
--   For the original spectrally negative Lévy X, adapted dividend D, prepayment left reserve and inclusive ruin-stop, the full negative-mark nonlinear Taylor remainder is integrable against a finite right-continuous predictable clock times the genuine source Lévy measure X.ν, and its signed total mass is exactly the time-clock integral of the stopped SpectrallyNegativeLevy.generatorIntegrand. This source-specific Fubini bridge uses the proved general-C² L1 envelope and source generator identity. It asserts no independent Poisson measure and no unproved sample compensator law.
-- source:
--   Canonical Proved 0e0663b1 actual stopped general C² predictable full negative source L1/L2 energy, a9270e22 source negative SFinite, 5e3be45e exact generator Taylor section; pinned Mathlib lintegral_prod, integral_prod and Integrable constructor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     (∫ p, HS p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
       ∫ p : ℝ≥0 × Ω,
         (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) ∂μ) := by sorry
