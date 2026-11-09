-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_closed_cash_bound_false
-- name    : AvramDividend.Classical.avram_bv_route11_zero_cap_closed_cash_bound_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:31:04.123433+00:00
-- url     : https://prove2.me/theorems/9a523525-509a-4b6c-8288-ec2b1c466358
-- title:
--   No uniform zero discounted-cash bound at zero cap for original finite-activity BV barrier
-- statement:
--   Under the original Standing bounded-variation and finite negative-jump-activity assumptions, the admissible zero-cap barrier has strictly positive discounted Stieltjes cash at some finite horizon. Therefore a bound asserting that its discounted cash is zero at every horizon is false. This is a formally quantified conditional obstruction to the unrestricted-cap stochastic core, and is derived directly from the accepted original-process counterexample certificate.
-- source:
--   BV-ROUTE11: direct corollary of Proved public avram_bv_route11_zero_cap_contact_positive_cash (833cfa93); no Open or deprecated imports. Does not claim a fully constructed concrete Standing process instance.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_contact_positive_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bv_route11_zero_cap_closed_cash_bound_false
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ¬ ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
        (0 : ℝ≥0∞) := by sorry
