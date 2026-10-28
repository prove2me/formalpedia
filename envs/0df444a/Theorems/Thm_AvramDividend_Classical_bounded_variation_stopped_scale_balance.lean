-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_variation_stopped_scale_balance
-- name    : AvramDividend.Classical.bounded_variation_stopped_scale_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T00:01:37.458956+00:00
-- url     : https://prove2.me/theorems/2bb529c8-d611-4c49-9460-1d4af4620ae8
-- title:
--   Bounded-variation stopped-scale balance for the two-sided exit integral
-- statement:
--   For a spectrally negative Levy process under the standing assumptions with a q-scale function W and finite-variation paths, the discounted two-sided up-exit integral in raw first-passage form, scaled by ofReal (W a), equals ofReal (W x) for 0 <= x <= a with 0 < a. This is the bounded-variation case of the stopped-scale balance: the exact missing link for the bounded-variation exit identity 494dbcd1 (which follows by the verified eq_div_iff division skeleton once this balance holds), hence for the 09663d0d case split and the barrier_strategy_value chain. No cyclic dependency: it assumes no Open exit theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007) two-sided exit / scale-function identities; bounded-variation case isolated as the precise open obligation of parent 494dbcd1-770a-49c0-986b-046103fab9c4 within mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bounded_variation_stopped_scale_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
