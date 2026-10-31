-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_stieltjes_Icc_discount_identity
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_discount_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T20:54:18.34382+00:00
-- url     : https://prove2.me/theorems/d0dcf81c-2f9f-4b82-b216-06713ec08441
-- title:
--   Actual BV post-payment reserve obeys closed-interval discounted Stieltjes integration by parts
-- statement:
--   For the actual bounded-variation Levy source and any admissible-shape dividend process, every globally Lipschitz test of the genuine post-payment reserve and nonnegative exponential discount obey a closed-interval Stieltjes integration-by-parts identity, with the starting left limit and ending right limit preserving the time-zero and later dividend jumps.
-- source:
--   Original postPayment_truncated_global_variation and discount_exp_global_variation, plus Mathlib BoundedVariationOn.setIntegral_Icc_leftLim_smul_vectorMeasure_eq_sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_discount_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hf : BoundedVariationOn f Set.univ,
        ∃ hg : BoundedVariationOn g Set.univ,
          ∀ a b : ℝ≥0, a ≤ b →
            (∫ᵛ t in Icc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.leftLim f a • Function.leftLim g a -
              (∫ᵛ t in Icc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
