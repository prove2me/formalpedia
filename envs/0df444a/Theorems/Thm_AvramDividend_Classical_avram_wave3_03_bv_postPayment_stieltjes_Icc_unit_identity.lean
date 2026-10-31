-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_stieltjes_Icc_unit_identity
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_unit_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:06:22.884392+00:00
-- url     : https://prove2.me/theorems/6694d8c4-bae3-47f2-b241-9e7230106210
-- title:
--   Original BV post-payment Stieltjes unit-weight identity with closed-interval boundary atoms
-- statement:
--   For the true bounded-variation Levy reserve controlled by any adapted dividend strategy and frozen at an arbitrary finite horizon, the unit-weight Stieltjes vector integral of a globally Lipschitz post-payment value test on a closed interval equals its right endpoint minus its left limit, thereby including the time-zero right-payment atom exactly.
-- source:
--   Pinned Mathlib BoundedVariationOn.vectorMeasure_Icc and VectorMeasure.setIntegral_const with Proved postPayment_truncated_global_variation. The positive-discount product rule is not imported by the pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_stieltjes_Icc_unit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        ∀ a b : ℝ≥0, a ≤ b →
          (∫ᵛ t in Icc a b, (1 : ℝ) ∂• hg.vectorMeasure) =
            Function.rightLim g b - Function.leftLim g a := by sorry
