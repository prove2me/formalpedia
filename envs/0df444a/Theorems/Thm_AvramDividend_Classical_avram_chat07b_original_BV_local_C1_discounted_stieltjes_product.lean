-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:04:55.061385+00:00
-- url     : https://prove2.me/theorems/921f2ec5-2881-480f-891e-56ba98d46fb6
-- title:
--   Original interior-C¹ stopped BV Lévy reserve satisfies exact discounted half-open Stieltjes product rule
-- statement:
--   For the actual standing spectrally negative Lévy process in its bounded-variation branch and original controlled dividend strategy, the stopped right-postpayment reserve stays within a positive compact band. The canonical merely interior C1 test w composes with that actual BV path; together with the globally BV exponential discount, the two true time paths satisfy the exact half-open vector-Stieltjes integration-by-parts identity for every interval, including singular dividends, simultaneous jumps, and initial rightLimit effects. Uses the independently accepted original BV C1 composition and the accepted genuine vector-measure Fubini exchange. No hypothetical probability space, stronger global C1/Lipschitz condition, or assumed stochastic payout inequality.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i), deterministic finite-variation controlled C1 product rule on actual stopped right-postpayment paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_postpayment_composition
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_stieltjes_Ioc_fubini_exchange
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_chat07b_original_BV_local_C1_discounted_stieltjes_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (cap lo hi : ℝ)
    (hlr : lo < hi) (hsub : Icc lo hi ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈ Icc lo hi) →
      let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
      let g : ℝ≥0 → ℝ := fun t =>
        w (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hf : BoundedVariationOn f Set.univ,
        ∃ hg : BoundedVariationOn g Set.univ,
          ∀ a b : ℝ≥0, a ≤ b →
            (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
              Function.rightLim f b • Function.rightLim g b -
              Function.rightLim f a • Function.rightLim g a -
              (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by sorry
