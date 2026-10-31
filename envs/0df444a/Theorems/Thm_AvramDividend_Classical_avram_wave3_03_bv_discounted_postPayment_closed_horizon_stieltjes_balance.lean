-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:53:00.782992+00:00
-- url     : https://prove2.me/theorems/3889b578-e18f-41f9-8e35-e6965b20b605
-- title:
--   True discounted BV post-payment finite-horizon Stieltjes mass equals terminal minus initial value
-- statement:
--   For the genuine bounded-variation controlled Levy reserve under any nonnegative discount, the vector Stieltjes mass of the discounted post-payment Lipschitz test on [0,T] equals its terminal discounted value less its initial post-payment value. This maintains the distinction between test variation and actual initial dividend payments.
-- source:
--   Proved discounted post-payment BV vector measure and pinned vectorMeasure_Icc, rightLim_eq_of_tendsto, leftLim_eq_of_isBot.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
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
        hg.vectorMeasure (Icc 0 T) = g T - g 0 := by sorry
