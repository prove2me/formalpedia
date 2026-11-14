-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
-- name    : AvramDividend.Classical.avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:34.428657+00:00
-- url     : https://prove2.me/theorems/863049b7-6862-42bb-9f51-8ab8588dab21
-- title:
--   Local uniform limits of one-sided right-continuous cutoff functions preserve right continuity
-- statement:
--   For functions on nonnegative time, locally uniform convergence on the right-sided neighbourhood of t preserves right continuity at t when every approximant is right-continuous at t.
-- source:
--   Pinned Mathlib continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt, uniform convergence right-neighbourhood criterion.

import Mathlib
open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- A locally uniform limit of functions right-continuous at the same time is right-continuous there. -/

theorem AvramDividend.Classical.avram_a24_rightcont_of_locally_uniform_rightcont_cutoffs_20261113
    (F : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hRight : ∀ n : ℕ, ContinuousWithinAt (F n) (Ici t) t)
    (hUniform : TendstoLocallyUniformlyOn F g atTop (Ici t)) :
    ContinuousWithinAt g (Ici t) t := by sorry
