-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_discounted_stopped_negative_taylor_product_eq_generator
-- name    : AvramDividend.Classical.avram_wave7_07_original_discounted_stopped_negative_taylor_product_eq_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:26:48.436757+00:00
-- url     : https://prove2.me/theorems/42b5060d-3dd6-41b0-ab2b-755c78db1402
-- title:
--   Original C² ruin-stopped Lévy negative-jump discounted generator drift product identity
-- statement:
--   For the original source X, x, D, P, filtration and Lévy measure with finite predictable clock μ, any nonnegative q and explicitly predictable source discount exp(-q t), the discounted stopped C2 negative-mark Taylor product integral equals the discounted integrated source generator negative-mark term. Discount bounded by one; exact truncation (-1,0), real original ruin time and prepayment left limit.
-- source:
--   W7-07 discounted source jump compensation application for W7-08 original Itô–Meyer

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_discounted_stopped_negative_taylor_product_eq_generator
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
    (q : ℝ) (hq : 0 ≤ q)
    (hdisc : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))) :
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      Real.exp (-(q * (r.1.1 : ℝ))) * HS r
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν) ∂μ) := by sorry
