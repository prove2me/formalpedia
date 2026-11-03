-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_true_clock_negative_generator_tails_auto_measurable
-- name    : AvramDividend.Classical.avram_wave7_07_original_true_clock_negative_generator_tails_auto_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:22:14.586007+00:00
-- url     : https://prove2.me/theorems/45cd89b0-539a-47a4-9910-aea8890bb222
-- title:
--   Original true-clock negative-generator L1 tails with automatic predictable mark-integral measurability
-- statement:
--   Under the original source predictable finite time clock, negative Lévy mark L1-tail convergence holds for every antitone sequence of Borel negative mark sets B n, without assuming measurable source mark integrals separately. Construct measurability from accepted joint predictable C² thinning and exact generator-kernel identification, then apply the accepted original true-clock tail limit.
-- source:
--   W7-07 original Lévy negative-jump compensated generator limit for W7-08; the only added finite measure assumption is explicit, no replacement stochastic model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_true_clock_negative_generator_tails_auto_measurable
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
    (hμ : μ Set.univ < ⊤)
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
