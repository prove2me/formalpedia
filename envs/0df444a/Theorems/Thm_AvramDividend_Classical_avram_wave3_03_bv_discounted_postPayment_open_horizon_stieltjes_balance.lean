-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_open_horizon_stieltjes_balance
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_open_horizon_stieltjes_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:05:07.988669+00:00
-- url     : https://prove2.me/theorems/d5bbe19d-b6c6-49b0-85a0-c5a4b3df5ea4
-- title:
--   True discounted BV post-payment Stieltjes mass on (0,T] equals terminal minus initial value
-- statement:
--   On the true bounded-variation controlled Levy process, the vector Stieltjes mass of a discounted Lipschitz test of the post-payment reserve on (0,T] is its terminal discounted value minus its initial post-payment value. The initial dividend remains separately present in the actual dividend measure.
-- source:
--   Proved source-level closed horizon Stieltjes balance and zero post-payment atom, together with pinned vector-measure disjoint-union additivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_open_horizon_stieltjes_balance
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
        hg.vectorMeasure (Ioc 0 T) = g T - g 0 := by sorry
