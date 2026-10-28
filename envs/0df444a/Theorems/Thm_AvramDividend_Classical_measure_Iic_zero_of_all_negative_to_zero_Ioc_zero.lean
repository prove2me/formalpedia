-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
-- name    : AvramDividend.Classical.measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:58:24.182983+00:00
-- url     : https://prove2.me/theorems/30103409-586a-4404-b4a1-510990034747
-- title:
--   Vanishing negative-to-zero Stieltjes windows eliminate the entire nonpositive half-line
-- statement:
--   If a real-time measure assigns zero mass to every half-open interval ending at time zero and starting at a strictly negative time, then it assigns zero mass to the whole nonpositive half-line. A countable increasing cover and measure subadditivity establish the result. This bridges local Stieltjes zero-window theorems to full stopped-measure support.
-- source:
--   Strong-Markov barrier support helper for child 79978d61-9d1f-4b20-b8a5-114797a8e380. Converts Proved runningSup_dividendMeasure_Ioc_nonpos_eq_zero (55945b02-bdc5-4c2b-a26e-c147b0481f0b) into the hνzero needed by translated-measure uniqueness 50431279-23d0-42be-b261-421a5476921e, including time zero.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
    (μ : Measure ℝ)
    (hwindow : ∀ s : ℝ, s < 0 →
      μ (Set.Ioc s (0 : ℝ)) = 0) :
    μ (Set.Iic (0 : ℝ)) = 0 := by
  sorry
