-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_generator_tails
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_generator_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:14:44.51941+00:00
-- url     : https://prove2.me/theorems/9522a74e-a187-4a36-9ce2-1325ba814476
-- title:
--   Canonical UBV admissible true-clock shrinking negative Lévy marks under exponential discount
-- statement:
--   For the exact original source process, canonical admissible UBV controlled reserve and physical predictable clock, prove that exponentially discounted negative-generator tail L¹ norms vanish as B_n decreases to ∅ inside strictly negative marks. The extended-real cap admits finite C² reserve localisation and exp(-q t), q≥0, is original predictable and bounded by one. This is the genuine source ν tail passage needed by W7-08 after stochastic marked-count compensation.
-- source:
--   W7-07 original-process discounted shrinking negative generator tails for W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_extended_cap_true_clock_negative_generator_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_generator_tails
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
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
    (q : ℝ) (hq : 0 ≤ q) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∀ n, Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in B n, JG (p,z) ∂X.ν))) →
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖Real.exp (-(q * (p.1 : ℝ))) * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by sorry
