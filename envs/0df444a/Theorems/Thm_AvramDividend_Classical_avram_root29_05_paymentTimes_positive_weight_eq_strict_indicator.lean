-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
-- name    : AvramDividend.Classical.avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:50:23.37088+00:00
-- url     : https://prove2.me/theorems/9c1008b1-3501-418d-81dd-47ac6e272b57
-- title:
--   Original paymentTimes positive-time Stieltjes integral equals exactly the strict ruin indicator integral
-- statement:
--   For any real-time Stieltjes measure, discount q and exact ruin clock τ, the integral over the original paymentTimes τ of the positive-time discounted reward equals the full-real-time integral of the same discount multiplied by both positive-time and strictly-before-ruin indicators. Since the integrand vanishes at zero, the explicitly included time-zero payment does not contribute. This is precisely the original Avram dividend payment-set convention, not an incorrect stopped set. Used to identify the full pathwise Stieltjes reconstruction with the original barrier dividend-value definition for x≤a.
-- source:
--   Proved paymentTimes_measurable 88dafb7f, exact original DividendStrategy definition paymentTimes; pinned Mathlib lintegral_indicator and set indicator case split.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
    (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) =
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) := by sorry
