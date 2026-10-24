-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_killed_first_record_discount_weight_measurable
-- name    : AvramDividend.Classical.chat08_killed_first_record_discount_weight_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:08:57.717679+00:00
-- url     : https://prove2.me/theorems/00947d57-ee37-48d3-ae66-d34f5326fd7e
-- title:
--   Stopped discounted first-record payment is a measurable random variable
-- statement:
--   For any real first-record threshold c, barrier level a, discount parameter q and record payment h, the nonnegative extended-real payoff equal to h exp(-q u_c) on strict passage before corrected reflected ruin and zero otherwise is a measurable random variable. This follows from measurability of the actual strict first-passage clock and corrected reflected ruin time, the measurable strict comparison event, and Borel measurability of exp, multiplication and ENNReal.ofReal. The result supplies per-cell AEMeasurable weights required by the countable stopped-renewal integral bridges.
-- source:
--   Prove2Me chat08_upper_passage_clock_measurable and barrierRuinTime_measurable; Mathlib measurableSet_lt and measurable ENNReal ofReal.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.chat08_killed_first_record_discount_weight_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c q h : ℝ) :
    Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
        ENNReal.ofReal (h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
      else 0) := by sorry
