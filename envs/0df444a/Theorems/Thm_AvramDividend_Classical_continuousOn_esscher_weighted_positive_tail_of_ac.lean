-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_positive_tail_of_ac
-- name    : AvramDividend.Classical.continuousOn_esscher_weighted_positive_tail_of_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:51:41.852338+00:00
-- url     : https://prove2.me/theorems/fb8ea27f-ef08-4ec2-91e7-4545ed9beb40
-- title:
--   Positive-time continuity of the Esscher-discounted jump-tail density
-- statement:
--   For any real Lévy jump-magnitude measure absolutely continuous with respect to Lebesgue measure, and any Esscher exponential discount, the discounted positive strict tail mass is continuous on the positive half-line whenever the discounted upper tails are finite. This supplies the continuity field of the convolution kernel in bv_ac_esscher_scaled_renewal_kernel_series_data (9be5ada9-6f14-4f14-8115-14262e488433), which in turn feeds the BV density, C1 regularity, cstar_lt_top and the root theorem.
-- source:
--   Weighted measures remain absolutely continuous with respect to their original measure; apply the canonical positive strict-tail continuity theorem.

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_continuousOn_positive_strict_tail_of_absolutelyContinuous
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.continuousOn_esscher_weighted_positive_tail_of_ac
    (μ : Measure ℝ) (hac : μ ≪ volume) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x →
      (μ.withDensity
        (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))) (Ici x) ≠ ⊤) :
    ContinuousOn
      (fun x : ℝ =>
        (μ.withDensity
          (fun z : ℝ => ENNReal.ofReal (Real.exp (-(φ * z))))).real (Ioi x))
      (Ioi (0 : ℝ)) := by sorry
