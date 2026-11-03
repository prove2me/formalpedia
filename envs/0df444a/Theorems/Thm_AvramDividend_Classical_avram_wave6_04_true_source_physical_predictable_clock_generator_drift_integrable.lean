-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_generator_drift_integrable
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_generator_drift_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:21:00.660816+00:00
-- url     : https://prove2.me/theorems/18af3416-95ab-4576-9da9-70b8bfac2287
-- title:
--   Actual source ruin-stopped negative Lévy generator drift is L1 on its physical predictable clock
-- statement:
--   For the real source spectrally negative Levy marks X.ν and prepayment controlled reserve Y at the predictable left limit, stopped at the actual ruinTime X x D and localised in the C2 interior, show the signed full negative-mark generator drift is Bochner integrable on a finite source predictable clock μ provided only that μ agrees with physical Lebesgue-time × P on predictable sets. The earlier Proved signed-drift L1 theorem is reused, with its exact lintegral transport derived from the physical-clock agreement. No claim is made that an arbitrary clock is the X.X jump compensator.
-- source:
--   Wave6 Chat04 source generator L1 by physical predictable clock identity and previously Proved c254b492 signed jump drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_lintegral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_generator_drift_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
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
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) μ := by sorry
