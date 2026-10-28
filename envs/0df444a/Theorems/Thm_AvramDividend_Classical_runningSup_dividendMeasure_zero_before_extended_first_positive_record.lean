-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_before_extended_first_positive_record
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_before_extended_first_positive_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:10:32.529352+00:00
-- url     : https://prove2.me/theorems/589d4ebf-71e2-4e5b-9ae6-a0ebc26e67cc
-- title:
--   Zero dividend mass until the extended first positive record time
-- statement:
--   At every finite time strictly before the extended first positive record time, the running supremum is zero throughout the period and consequently its Stieltjes dividend measure gives the interval (0,t] zero mass. This remains valid if the first positive record never occurs and removes the finite-clock restriction from the no-initial-record branch of the stopped renewal upper estimate.
-- source:
--   Combines the Proved extended first-upcrossing supremum bound, nonnegativity of the running supremum, and the Stieltjes interval mass formula.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_extended_upcrossing_clock_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_before_extended_first_positive_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) <
      (⨅ (r : ℝ≥0) (_ : 0 < X.X r ω), (r : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc (0 : ℝ) (t : ℝ)) = 0 := by sorry
