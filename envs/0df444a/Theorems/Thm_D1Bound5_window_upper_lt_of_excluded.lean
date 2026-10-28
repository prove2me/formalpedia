-- Prove2me | Theorems.Thm_D1Bound5_window_upper_lt_of_excluded
-- name    : D1Bound5.window_upper_lt_of_excluded
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:45.419467+00:00
-- url     : https://prove2.me/theorems/42a1ba05-f190-44ba-b408-99585e303d67
-- title:
--   Leaving an excluded closed interval through its upper endpoint
-- statement:
--   Let $L,U,D$ be real numbers. If $L\le D$ and $D$ does not belong to the closed interval specified by $L\le D\le U$, then
--   $$U<D.$$
--   No assumption that $L\le U$ is required.
-- source:
--   D1Bound5/AllLargeWindows.lean, D1Bound5.window_upper_lt_of_excluded, lines 36-38; original file SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic

theorem D1Bound5.window_upper_lt_of_excluded (w : ℝ × ℝ) (D : ℝ)
    (hex : ¬ (w.1 ≤ D ∧ D ≤ w.2)) (hlo : w.1 ≤ D) : w.2 < D := by sorry
