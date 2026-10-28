-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim
-- name    : AvramDividend.Classical.dividendMeasure_Iic_zero_of_monotone_rightLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:07:39.582025+00:00
-- url     : https://prove2.me/theorems/bef57193-c353-4e51-8c32-e9c62d4040c6
-- title:
--   Right-limit-fixed dividend paths carry no Stieltjes mass at nonpositive real times
-- statement:
--   For an arbitrary real-time extension of a monotone dividend path that is equal to its right limit at every real time, the Stieltjes dividend measure has zero mass on the entire nonpositive half-line. Each negative-to-zero window has identical dividend values at both endpoints because nonpositive real times map to time zero; use the proved exact half-open Stieltjes interval formula and countable support lemma.
-- source:
--   Direct bridge for W-free strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380. Discharges the nonpositive-support assumptions in pathwise measure translation theorem 3093890e-4ed7-4198-8491-5f41d268763c once monotonicity and right-continuity of the actual barrier and shifted record regulators are established.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_all_negative_to_zero_Ioc_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Iic_zero_of_monotone_rightLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hm : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r =
        D r.toNNReal ω) :
    (dividendMeasure D ω) (Set.Iic (0 : ℝ)) = 0 := by
  sorry
