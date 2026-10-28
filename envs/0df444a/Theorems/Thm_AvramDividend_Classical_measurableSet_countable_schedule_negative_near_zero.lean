-- Prove2me | Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero
-- name    : AvramDividend.Classical.measurableSet_countable_schedule_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:18:06.423177+00:00
-- url     : https://prove2.me/theorems/311860a5-0c30-4675-82c4-ec153d1b2d59
-- title:
--   Near-zero negative observations along countable time grids form a measurable set of sample paths
-- statement:
--   For any two sequences of nonnegative times and positive-horizon thresholds (not assumed positive), the set of real-valued sample paths that attain a negative value at some selected time below each horizon is measurable in the product measurable space. This supplies the countable-cylinder event needed to apply proved strong Markov whole-path law transfer to negative-near-zero behaviour. The proof is a countable intersection of countable unions of Borel one-coordinate inequalities. Establishing equivalence to all-time downward regularity separately requires right-continuity and density of the chosen schedule.
-- source:
--   Countable-product measurable spaces and Levy-process near-zero regularity; preparatory event for the reflected-excursion-height argument in Kuznetsov, Kyprianou and Rivero (2013) Section 2.3.

import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.measurableSet_countable_schedule_negative_near_zero
    (times horizons : ℕ → ℝ≥0) :
    MeasurableSet
      {f : ℝ≥0 → ℝ | ∀ n : ℕ, ∃ m : ℕ,
        times m < horizons n ∧ f (times m) < 0} := by sorry
