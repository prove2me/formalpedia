-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_local_open_intervals
-- name    : AvramDividend.Classical.contDiffOn_one_Ioi_of_local_open_intervals
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:53:46.191565+00:00
-- url     : https://prove2.me/theorems/a971a6b7-a9d4-4c45-96e7-0269d0c94183
-- title:
--   Patch local C1 regularity on positive intervals to the positive half-line
-- statement:
--   A real function is continuously differentiable on (0,∞) whenever every strictly positive point has a strictly positive open-interval neighbourhood on which the function is continuously differentiable. This patches Gaussian Neumann-series estimates on compact positive intervals to global scale-function regularity.
-- source:
--   Pinned Mathlib contDiffOn_of_locally_contDiffOn in Mathlib.Analysis.Calculus.ContDiff.Defs, with positive interval inclusion.

import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set

theorem AvramDividend.Classical.contDiffOn_one_Ioi_of_local_open_intervals
    (f : ℝ → ℝ)
    (hlocal : ∀ x : ℝ, 0 < x →
      ∃ a b : ℝ, 0 < a ∧ a < x ∧ x < b ∧ ContDiffOn ℝ 1 f (Ioo a b)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by sorry
