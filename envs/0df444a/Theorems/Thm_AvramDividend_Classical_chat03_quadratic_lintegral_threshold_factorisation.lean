-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_quadratic_lintegral_threshold_factorisation
-- name    : AvramDividend.Classical.chat03_quadratic_lintegral_threshold_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:36:27.483201+00:00
-- url     : https://prove2.me/theorems/1b99c3a5-9462-4ed0-a394-cc633be40433
-- title:
--   Positive threshold factorisation of a quadratic Lebesgue integral
-- statement:
--   For any real-valued function on a measurable space and any positive threshold R, the nonnegative Lebesgue integral of its square divided by R equals its quadratic nonnegative integral divided by ENNReal.ofReal R. This remains valid when the quadratic moment is infinite and requires no measurability premise for Y.
-- source:
--   ENNReal.ofReal_div_of_pos and the pinned nonmeasurable lintegral_mul_const' lemma, using positivity to ensure that the inverse threshold is finite.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Inv

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.chat03_quadratic_lintegral_threshold_factorisation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 < R) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P) =
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) / ENNReal.ofReal R := by sorry
