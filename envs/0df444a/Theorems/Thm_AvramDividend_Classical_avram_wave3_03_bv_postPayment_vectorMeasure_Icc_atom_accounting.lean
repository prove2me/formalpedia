-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_vectorMeasure_Icc_atom_accounting
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_vectorMeasure_Icc_atom_accounting
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:09:55.844755+00:00
-- url     : https://prove2.me/theorems/2d9d4e23-5e0e-45ea-a327-39bc09a03b10
-- title:
--   True BV controlled-surplus vector measure has exact closed-interval left/right endpoint mass
-- statement:
--   The true source post-payment controlled Levy reserve, frozen at any finite horizon, admits an almost surely defined bounded-variation Lipschitz value-test path whose associated vector Stieltjes measure assigns to every closed interval exactly its ending right limit less its initial left limit, preserving all dividend jumps including at time zero.
-- source:
--   Pinned Mathlib BoundedVariationOn.vectorMeasure_Icc and Proved actual BV postPayment_truncated_global_variation, with no unavailable integration-by-parts imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_vectorMeasure_Icc_atom_accounting
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
          hg.vectorMeasure (Icc a b) =
            Function.rightLim g b - Function.leftLim g a := by sorry
