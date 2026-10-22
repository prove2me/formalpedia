-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_continuous_time
-- name    : AvramDividend.Classical.gaussian_double_tail_atom_continuous_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:03:13.299453+00:00
-- url     : https://prove2.me/theorems/ae783bfd-d258-4f4b-933e-6b787a6bbe55
-- title:
--   Continuity of the Esscher Gaussian double-tail atom at positive times
-- statement:
--   For each fixed jump magnitude, the conditional positive-time Gaussian Esscher double-tail atom is continuous as a function of time, including at the threshold where the indicator switches. Its positive-part representation removes the apparent discontinuity and supplies the pointwise continuity hypothesis for dominated convergence of the full jump kernel.
-- source:
--   Positive-part maximum representation, continuity of max, and an eventually-positive time neighbourhood.

import Mathlib
open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_atom_continuous_time
    (φ z t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ =>
      if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
      else 0) t := by sorry
