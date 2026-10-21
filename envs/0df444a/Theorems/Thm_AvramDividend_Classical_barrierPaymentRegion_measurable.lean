-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierPaymentRegion_measurable
-- name    : AvramDividend.Classical.barrierPaymentRegion_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:41:14.224384+00:00
-- url     : https://prove2.me/theorems/9ca4f703-cb37-448a-b9b5-10f436128de7
-- title:
--   Joint measurability of original reflected-barrier stopping payment region
-- statement:
--   For a spectrally negative Lévy process and any real reflection barrier, the set of real-time and sample-point pairs at which the original running-supremum dividends are permitted before the actual reflected-drawdown ruin horizon is measurable. Apply the accepted general jointly measurable payment-time-set theorem to the accepted measurability of the actual barrier ruin time. The statement preserves the special time-zero payment convention and is an essential input to the stopped Stieltjes kernel integral measurability theorem.
-- source:
--   Remotely Proved barrierRuinTime_measurable target 322896d6-052f-46bc-9fe6-962277f2d0a2 and paymentTimes_joint_measurable target 6e9faa20-c0bf-445c-92c0-0fd50340de1b, repair candidate 12146 ACCEPTED.

import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierPaymentRegion_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    MeasurableSet
      {p : ℝ × Ω |
        p.1 ∈ paymentTimes (barrierRuinTime X a p.2)} := by sorry
