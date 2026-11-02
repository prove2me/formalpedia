-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
-- name    : AvramDividend.Classical.avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:08:51.672109+00:00
-- url     : https://prove2.me/theorems/0bd4e585-381d-4b45-96c8-8d73faf747be
-- title:
--   Original stopped negative Lévy Taylor kernel has full L¹/L² physical energy under any predictable contraction
-- statement:
--   For the actual source X.X, original dividend strategy D and inclusive ruinTime, all-negative-mark compensated nonlinear C² Taylor remainder with prepayment left-limit surplus retains physical product L¹ and L² finiteness under any bounded rightCont predictable multiplicative weight a satisfying |a|≤1, including signed weights and randomly stopped q-discounts. The proof uses the exact already-Proved original-source physical product L1/L2 energies and pointwise |a HS|≤|HS|, (a HS)^2≤HS^2, without ν large-negative first moment, generic jump compensator assumptions, or Chat02 martingale isometry.
-- source:
--   Wave6 Chat04 same-source arbitrary rightCont predictable contraction L1/L2 product negative-mark energy. Builds from Proved 955eaa85 and 2d67e34c, no hFuture or isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by sorry
