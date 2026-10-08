-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_split_at
-- name    : AvramDividend.Classical.runningSup_split_at
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:12:24.490031+00:00
-- url     : https://prove2.me/theorems/05689e42-011e-4a4b-a169-02fdf64aa6f1
-- title:
--   Split a real-valued running supremum across two adjoining time intervals
-- statement:
--   For any real-valued function of nonnegative time bounded above on [0,u+t], its running supremum over [0,u+t] equals the maximum of its suprema over [0,u] and [u,u+t]. The intervals share exactly the endpoint u, avoiding a discontinuous endpoint gap. This deterministic pathwise identity is needed to express the post-barrier increment dividend process in terms of the shifted Lévy path.
-- source:
--   Pinned Mathlib csSup_union for bounded nonempty real sets, image_union, and elementary closed-interval decomposition over nonnegative time.

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_split_at
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t))) :
    sSup (f '' Set.Icc 0 (u + t)) =
      max (sSup (f '' Set.Icc 0 u))
          (sSup (f '' Set.Icc u (u + t))) := by sorry
