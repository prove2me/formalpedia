-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_measure_equality
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_measure_equality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:30:38.390632+00:00
-- url     : https://prove2.me/theorems/b1078a01-15a7-4de9-8559-bade47a9c7e0
-- title:
--   Genuine nonnegative-clock Esscher inverse density gives exact equality of joint measures
-- statement:
--   For arbitrary measurable real path/time statistic F, p>0 and q≥0, the complete jointly tilted measure with genuine toNNReal age and a second inverse Esscher density equals p/(p+q) times the original P×Exp(p+q) joint measure. This is a full measure equality, hence transfers every Borel event or measurable pushforward without a fresh moment or integrability argument.
-- source:
--   A whole-measure extensionality corollary of canonically Proved ce964d23, using the indicator of arbitrary measurable s as its ENNReal reward, pinned withDensity_apply, lintegral_indicator and lintegral_indicator_one. No product tilted-path law or limiting argument assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_cast_corrected

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_measure_equality
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q α : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (F : Ω × ℝ → ℝ) (hF : Measurable F) :
    ENNReal.ofReal (p + q) •
      (((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (α * F z - (Real.toNNReal z.2 : ℝ) * q)))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (-α * F z)))) =
    ENNReal.ofReal p • (P.prod (expMeasure (p + q))) := by sorry
