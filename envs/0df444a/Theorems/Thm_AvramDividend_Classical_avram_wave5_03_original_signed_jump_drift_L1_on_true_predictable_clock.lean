-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
-- name    : AvramDividend.Classical.avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:12:56.15747+00:00
-- url     : https://prove2.me/theorems/c254b492-43ea-4b98-8f84-33a7c8bc65d6
-- title:
--   Original stopped signed nonlinear Lévy jump-generator drift is L1 on the genuine finite predictable clock
-- statement:
--   The original source signed generator drift is not merely integrable against an invented compensator. Canonical 03-B 2352690b proves predictability for the actual controlled left-limit prepayment reserve and true ruin stop. Canonical 03-B 14b0f678 proves its finite physical-time times original-P first absolute moment. The exact predictable-lintegral equality is the canonical 04-B 16857b34 finite-horizon clock. Transport of the ENorm integral establishes genuine Bochner L1 on that same predictable clock. This supplies the negative-jump drift integrability ingredient of 732738fd and the stopped HJB reward-budget chain needed by corrected BV ef7e6c20 and UBV 429e17ca, without claiming an unproved compensator theorem.
-- source:
--   Proved 2352690b predictability, Proved 14b0f678 actual physical L1, Proved 16857b34 exact predictable clock; source BV ef7e6c20 and corrected UBV 429e17ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_generator_signed_drift_L1_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
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
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : ∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
      Measurable[𝓕.rightCont.predictable] f →
      (∫⁻ p, f p ∂μ) =
        (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) μ := by sorry
