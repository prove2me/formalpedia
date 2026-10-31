-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T20:56:33.774952+00:00
-- url     : https://prove2.me/theorems/42a41b3e-df03-4f5d-b520-bb3fbba7fab7
-- title:
--   True BV post-payment reserve satisfies discounted Stieltjes integration by parts
-- statement:
--   For the actual standing bounded-variation spectrally negative Levy process with any dividend strategy, every globally Lipschitz value test of the original post-payment reserve, frozen at a finite horizon, and any nonnegative exponential discount satisfy an exact Stieltjes integration-by-parts formula on each half-open time interval, including discontinuous dividend atoms through left and right limits.
-- source:
--   Mathlib BoundedVariationOn.setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub, original BV postPayment_truncated_global_variation, and discount_exp_global_variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Ioc_discount_identity
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
            (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.rightLim f a • Function.rightLim g a -
              (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
