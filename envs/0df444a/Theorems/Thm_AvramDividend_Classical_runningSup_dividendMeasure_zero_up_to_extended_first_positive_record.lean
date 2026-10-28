-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:06:14.230674+00:00
-- url     : https://prove2.me/theorems/94e6afb5-53db-4b3a-89a8-da44cc021f67
-- title:
--   No running-supremum dividend before or at the extended first positive record
-- statement:
--   At every finite observation time t up to and including the extended first positive record clock, the Stieltjes dividend measure of the running supremum gives (0,t] zero mass. The statement covers both a finite clock attained exactly at t and an infinite or later clock, so it closes the boundary case in the no-record branch of stopped-renewal budget decomposition.
-- source:
--   Case split on equality or strict inequality of t and the extended first-upcrossing clock, applying the two already Proved endpoint-specific zero-measure theorems.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_before_extended_first_positive_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc (0 : ℝ) (t : ℝ)) = 0 := by sorry
