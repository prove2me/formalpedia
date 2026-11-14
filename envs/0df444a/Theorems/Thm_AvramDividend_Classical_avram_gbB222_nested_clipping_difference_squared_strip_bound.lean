-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB222_nested_clipping_difference_squared_strip_bound
-- name    : AvramDividend.Classical.avram_gbB222_nested_clipping_difference_squared_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:55:54.446008+00:00
-- url     : https://prove2.me/theorems/0d9c20d7-0f9a-4f9f-901c-c64386045817
-- title:
--   Squared error between nested gradient clips is controlled by boundary-strip indicator
-- statement:
--   For a uniformly bounded reward derivative on a containing clipping band, the squared difference between two nested clipped gradients is at most four times the squared amplitude bound, multiplied by the indicator of the two spatial boundary strips. Hence the error vanishes off those strips and admits an occupation-integral bound.
-- source:
--   Bridge from new B220 selected clipping Gaussian L2 Cauchy to original fixed clipping B65; builds on B221 to quantify L2 cutoff changes by near-boundary occupation.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB222_nested_clipping_difference_squared_strip_bound
    (w : ℝ → ℝ) (a a' b' b B : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (y : ℝ) :
    ((if y ∈ Set.Icc a b then deriv w y else 1) -
      (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by sorry
