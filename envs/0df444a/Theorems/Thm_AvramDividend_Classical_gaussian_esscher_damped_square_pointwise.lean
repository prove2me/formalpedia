-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_square_pointwise
-- name    : AvramDividend.Classical.gaussian_esscher_damped_square_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:36:40.516445+00:00
-- url     : https://prove2.me/theorems/a8063c69-f417-4a85-8c5e-62d33500c463
-- title:
--   Exponential damping of quadratic positive jumps
-- statement:
--   Pointwise quadratic damping estimate, splitting at z=1 and using u ≤ exp u for u≥0.
-- source:
--   Elementary exponential inequality and Esscher tail domination

import Mathlib
open Set

theorem AvramDividend.Classical.gaussian_esscher_damped_square_pointwise (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) : Real.exp (-(φ * z)) * z ^ 2 ≤ (1 + 2 / φ) * (Real.exp (-(φ * z / 2)) * min (z ^ 2) z) := by sorry
