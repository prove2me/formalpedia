-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_requires_positive_boundary_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_requires_positive_boundary_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:26:51.529209+00:00
-- url     : https://prove2.me/theorems/9cffc899-9e8a-453c-8d4a-b107216ab4ed
-- title:
--   Uniform zero-cap finite-activity BV cash bounds require a strictly positive boundary allowance
-- statement:
--   For a genuine Standing bounded-variation spectrally negative Lévy process with finite negative-jump activity, the canonical original zero-barrier dividend control started with reserve zero has positive expected complete Stieltjes cash at a finite horizon. Therefore, if every finite natural-horizon original expected cash integral is bounded by ENNReal.ofReal W for a fixed real boundary allowance W, necessarily W>0. This is an exact source-faithful necessary condition on a zero-cap uniform bound and shows that the weaker premise W≥0 admits failure at W=0. It is conditional on the stated source existence assumptions, and places no restriction on the corrected positive-cap parent.
-- source:
--   Direct contraposition from Proved original-process finite-activity positive finite-horizon Stieltjes cash 09bbe99b-9773-470f-8348-ab31e25fb1c8, and ENNReal.ofReal_eq_zero. No Open imports or surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_requires_positive_boundary_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    0 < W := by sorry
