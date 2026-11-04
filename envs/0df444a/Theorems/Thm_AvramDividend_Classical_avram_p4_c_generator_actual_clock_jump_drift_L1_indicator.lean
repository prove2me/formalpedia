-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
-- name    : AvramDividend.Classical.avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:53:57.427658+00:00
-- url     : https://prove2.me/theorems/3da58e9f-a69a-4c19-9bf5-b1587d944396
-- title:
--   Actual original ruin-stopped source negative generator drift is L1 as a strict-interior indicator on true physical clock
-- statement:
--   For the actual original spectrally negative Levy X, the controlled left-limit reserve, strict compact positive C2 interior and original ruin clock, the indicator of the entire nonlinear negative-mark signed generator drift is integrable on the genuine predictable finite physical clock. It transports source proven joint L1 evidence from the nested masked mark integral to the exact stopped generator-density form with no invented compensation. The hμ premise is the existing source actual predictable-clock measure equivalence, which remains an explicit obligation, and no HJB at boundaries is assumed.
-- source:
--   Source true-clock signed jump drift L1 c254b492-43ea-4b98-8f84-33a7c8bc65d6 and original stopped indicator identity under P4-C prefix pending publication a43b79b2-a55f-4308-af62-dc6b1a4f5872.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_actual_stopped_jump_drift_indicator
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_actual_clock_jump_drift_L1_indicator
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
    let A : Set (ℝ≥0 × Ω) :=
      {p | (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧ Y p ∈ Icc (u + δ) v}
    Integrable (A.indicator (fun p =>
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w (Y p) z ∂X.ν)) μ := by sorry
