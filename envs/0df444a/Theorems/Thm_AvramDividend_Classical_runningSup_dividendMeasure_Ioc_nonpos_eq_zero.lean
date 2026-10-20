-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_nonpos_eq_zero
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_nonpos_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:24:37.722607+00:00
-- url     : https://prove2.me/theorems/55945b02-bdc5-4c2b-a26e-c147b0481f0b
-- title:
--   No actual reflected dividend Stieltjes mass on intervals ending at nonpositive times
-- statement:
--   The actual running supremum dividend measure gives zero mass to any half-open real-time interval whose endpoints are both nonpositive. This follows from the proved exact Stieltjes measure interval identity and the constant real-time extension of the regulator prior to time zero. It is a direct interval-level zero measure fact supporting stopped Stieltjes partition arguments.
-- source:
--   Remotely Proved runningSup_dividendMeasure_Ioc_eq_record_increment, theorem UUID 7343971b-047e-4925-9fa7-7ee76f6a2b23.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_nonpos_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ) (hs : s ≤ 0) (ht : t ≤ 0) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) = 0 := by sorry
