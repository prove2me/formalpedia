-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
-- name    : AvramDividend.Classical.avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:27:19.03443+00:00
-- url     : https://prove2.me/theorems/eeeff969-2beb-44dd-a7b6-c9ea25bc0055
-- title:
--   Actual source weighted negative generator cutoff tails vanish on the true predictable clock
-- statement:
--   For the actual source Levy measure X.ν, ruin-stopped predictable left-limit prepayment surplus, interior C2 localisation and a predictable bounded weight rho, transport vanishing absolute L1 signed negative-mark cutoff tails from the original physical-time × P clock to the true source predictable clock μ. Require the signed weighted cutoff drift to be predictable and setwise clock agreement. This is the direct clock version of the already proved weighted physical tail lemma, with no assertion that an arbitrary clock compensates the source jumps.
-- source:
--   Wave6 Chat04: source weighted cutoff generator L1 from a5242e78 and actual physical predictable lintegral equality 504eb909.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_generator_negative_mark_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_lintegral_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A predictable discount bounded by one contracts the actual physical
original-source nonlinear generator L1 small-mark drift tail. -/

theorem AvramDividend.Classical.avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
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
    (∀ n, Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => ρ p *
        (∫ z in B n, JG (p,z) ∂X.ν))) →
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by sorry
