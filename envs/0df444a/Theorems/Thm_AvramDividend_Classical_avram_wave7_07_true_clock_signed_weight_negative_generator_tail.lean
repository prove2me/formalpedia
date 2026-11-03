-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_signed_weight_negative_generator_tail
-- name    : AvramDividend.Classical.avram_wave7_07_true_clock_signed_weight_negative_generator_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:07:01.129629+00:00
-- url     : https://prove2.me/theorems/c1a95b55-5351-411e-b2a3-7b365e8c2900
-- title:
--   True-clock original Lévy C² negative generator tails vanish under arbitrary signed predictable unit contractions
-- statement:
--   For the exact original spectrally negative Lévy source and its original controlled left-limit surplus, any possibly signed predictable unit-bounded multiplier a has vanishing weighted signed negative-mark generator tail in L1 of the true finite-horizon predictable physical clock, with no additional per-cutoff measurability hypothesis. The canonical Lévy generator small-mark truncation and actual inclusive ruin stop are unchanged. This extends the accepted nonnegative-weight true-clock theorem 39cab1c9 using |a| and the norm invariance of real multiplication.
-- source:
--   Wave7 Chat07 signed true-clock source generator tail, from Proved 39cab1c9 and Real.enorm_abs. Physical analog 4395ea15 is already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_true_clock_signed_weight_negative_generator_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
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
    (a : ℝ≥0 × Ω → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖a p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by sorry
