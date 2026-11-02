-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:38:30.872819+00:00
-- url     : https://prove2.me/theorems/2a64513d-f218-48ad-9a83-dace751a1026
-- title:
--   Original source generatorIntegrand full negative signed predictable quadratic mark energy tails
-- statement:
--   On the original stopped source prepayment reserve, signed predictable contraction and any finite rightCont predictable μ, the canonical SpectrallyNegativeLevy.generatorIntegrand quadratic L2 negative-mark energy tail vanishes for arbitrary B_n↓∅. This follows from the actual pointwise source kernel equality e336f7e2 and original Taylor L2 iInf theorem cc000c72 via a signed contraction. It keeps ruinTime inclusive, the negative extension and mark cutoff z>-1. It does not assert the original source jump count predictable compensator.
-- source:
--   Wave6 Chat04 generator-kernel transfer of full negative C2 source L2 mark tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail
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
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
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
