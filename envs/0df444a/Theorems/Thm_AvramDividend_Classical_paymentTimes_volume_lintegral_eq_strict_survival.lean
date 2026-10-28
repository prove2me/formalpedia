-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_volume_lintegral_eq_strict_survival
-- name    : AvramDividend.Classical.paymentTimes_volume_lintegral_eq_strict_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:10:08.506569+00:00
-- url     : https://prove2.me/theorems/e64cd4ee-d73f-4279-accb-0432ac68ff28
-- title:
--   Drift-volume payout on prescribed payment times equals strict positive-time survival integral
-- statement:
--   For any extended nonnegative ruin horizon, integration against Lebesgue time on the actual original paymentTimes set coincides with integration over strictly positive real times of the same weight restricted to survival. The only difference between these sets is the possible singleton time zero, which has Lebesgue measure zero. This deterministic lemma handles zero and infinite horizons without assumptions on the dividend process.
-- source:
--   Mathlib Lebesgue indicator integration and Prove2Me paymentTimes measurable; canonical Avram Dividend dividend-payment convention.

import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_volume_lintegral_eq_strict_survival
    (σ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ, w t ∂volume) =
    (∫⁻ t in Ioi (0 : ℝ),
      (if ENNReal.ofReal t < σ then w t else 0) ∂volume) := by sorry
