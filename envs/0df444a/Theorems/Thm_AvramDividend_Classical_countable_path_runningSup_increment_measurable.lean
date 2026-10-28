-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_path_runningSup_increment_measurable
-- name    : AvramDividend.Classical.countable_path_runningSup_increment_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:31:53.282268+00:00
-- url     : https://prove2.me/theorems/11a24f6f-755d-4f4d-b5a3-76e2a4793454
-- title:
--   Measurable countable-time supremum of path increments
-- statement:
--   For any countable sequence of observation times, the nonnegative running supremum of a path's increments relative to its value at time zero is measurable on the product path space. The countable supremum uses ENNReal.ofReal and provides the measurable reward-skeleton ingredient required before applying stopped-path strong Markov factorisation to reflected barrier dividends. No right-continuity assumptions are needed for this measurability statement, while cadlag equivalence to the continuous-time regulator is a separate obligation.
-- source:
--   Measurability prerequisite for the dyadic/rational running-supremum Stieltjes reward reconstruction in Avram, Palmowski and Pistorius (2007), Proposition 1. Downstream target 79978d61-9d1f-4b20-b8a5-114797a8e380. The theorem is independent of the two-sided-exit identity and prevents uncountable-product measurability assumptions.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_path_runningSup_increment_measurable
    (times : ℕ → ℝ≥0) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ n : ℕ, ENNReal.ofReal (f (times n) - f 0)) := by
  sorry
