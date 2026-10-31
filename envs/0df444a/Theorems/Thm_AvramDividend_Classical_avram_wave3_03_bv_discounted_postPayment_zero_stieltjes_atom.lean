-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:19:41.963298+00:00
-- url     : https://prove2.me/theorems/0445b142-983f-4f3a-8b3f-e9e8c608e5c3
-- title:
--   Discounted post-payment BV Stieltjes measure has zero singleton mass at the origin
-- statement:
--   The real original post-payment reserve, frozen at any finite horizon and tested against a globally Lipschitz value function with exponential discount, starts right-continuously at time zero. Its vector Stieltjes measure therefore has zero singleton mass at zero. Any actual time-zero dividend jump must be accounted for separately by the original dividend measure; it is already reflected in the post-payment starting value.
-- source:
--   Proved postPaymentReserve_cadlag_adapted and discounted postPayment Ioc atom accounting, pinned Function.ContinuousWithinAt.rightLim_eq and leftLim_eq_of_isBot.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
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
        hg.vectorMeasure ({0} : Set ℝ≥0) = 0 := by sorry
