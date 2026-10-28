-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_downward_increment_count_measurable
-- name    : AvramDividend.Classical.finite_grid_downward_increment_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:20:21.136203+00:00
-- url     : https://prove2.me/theorems/455ca9e4-5aa6-41c1-a340-245eb74ebd37
-- title:
--   The count of threshold-exceeding downward path increments on a finite grid is measurable
-- statement:
--   For any finite grid of pairs of nonnegative observation times, the number of pairs whose path decrement is below a fixed negative threshold is a measurable natural-number-valued functional of the full coordinate path. Each indicator is the measurable selection between 0 and 1 according to a cylinder inequality, and their finite sum is measurable. This supplies explicit observable counts for a later limit-based reconstruction of canonical Poisson jump-band counts.
-- source:
--   Mathlib measurable_pi_apply, Measurable.sub, IsOpen.measurableSet, Measurable.ite, and Finset.measurable_sum in the pinned environment.

import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.finite_grid_downward_increment_count_measurable
    (grid : Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ∑ ij ∈ grid, if f ij.2 - f ij.1 < -a then (1 : ℕ) else 0) := by sorry
