-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomly_stopped_discount_generator_negative_mark_L2_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_randomly_stopped_discount_generator_negative_mark_L2_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:00:45.971935+00:00
-- url     : https://prove2.me/theorems/157b96f3-e4b8-4c71-be2d-ef945a5a9866
-- title:
--   Original stopped-discount source generator quadratic negative-mark tails on the physical predictable clock
-- statement:
--   For the actual source X.ν and original inclusive ruinTime, a genuine stopped exp(-qt) discount weight is predictable and bounded by one. Hence any decreasing measurable negative real Lévy-mark bands with empty intersection have vanishing quadratic nonlinear generator energy against the finite physical predictable μ clock, including small compensated jumps and large uncorrected negative jumps. This is a directly importable discounted instance of the already Proved signed predictable L2 generator mark-tail theorem.
-- source:
--   Wave 6 Chat 04 source C2 nonlinear generator L2 mark-tail discounted stopping specialisation; reuses Proved 2a645 and 7b979.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_randomly_stopped_discount_generator_negative_mark_L2_tail
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
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
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B)
      (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * JG (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
