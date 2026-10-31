-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:15:18.670836+00:00
-- url     : https://prove2.me/theorems/5ceaf5b7-4311-4d37-8d90-3bd8a7857e43
-- title:
--   Discounted true BV reserve has exact open-closed Stieltjes mass and singleton atoms
-- statement:
--   For the genuine bounded-variation controlled Levy reserve, the exponentially discounted globally Lipschitz value-test path has an almost surely well-defined vector Stieltjes measure, whose mass on every open-closed interval is the right-limit increment and whose singleton mass is precisely its left/right jump, including the initial time-zero dividend atom.
-- source:
--   Pinned Mathlib BoundedVariationOn.vectorMeasure_Ioc and vectorMeasure_singleton together with remotely Proved original source postPayment_truncated_global_variation and discount_exp_global_variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discount_exp_global_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        ∀ a b : ℝ≥0, a ≤ b →
          hg.vectorMeasure (Ioc a b) =
            Function.rightLim g b - Function.rightLim g a ∧
          hg.vectorMeasure ({a} : Set ℝ≥0) =
            Function.rightLim g a - Function.leftLim g a := by sorry
