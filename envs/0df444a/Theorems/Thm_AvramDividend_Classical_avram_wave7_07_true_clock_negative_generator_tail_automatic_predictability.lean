-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability
-- name    : AvramDividend.Classical.avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:38:56.091972+00:00
-- url     : https://prove2.me/theorems/39cab1c9-75d0-412c-a628-1dccafcfda04
-- title:
--   Actual stopped negative Lévy generator tails vanish on the true predictable clock without a separate signed-cutoff measurability hypothesis
-- statement:
--   On the actual spectrally negative Lévy source and true finite physical predictable clock, the bounded signed predictable-weight negative-mark generator tail vanishes in L1 for any decreasing measurable negative cutoff to the empty set. Predictability of each signed cutoff drift follows automatically from original-source joint Taylor kernel measurability, removing the explicit extra hypothesis in the accepted eeeff969 theorem.
-- source:
--   Wave 7 Chat 07 exact source true-clock negative generator tail with automatic cutoff measurability. Uses accepted eeeff969 and one source-faithful independent new helper 79c84e83 (Open pending proof at authoring).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_generator_signed_negative_mark_cutoff_predictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability
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
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by sorry
