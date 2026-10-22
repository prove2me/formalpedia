-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_large_uniform
-- name    : AvramDividend.Classical.gaussian_esscher_drift_large_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:19:25.961077+00:00
-- url     : https://prove2.me/theorems/a9787680-270d-42fe-a75a-1c6b5711a19f
-- title:
--   Uniform large-jump bound for exponential Esscher drift correction
-- statement:
--   For positive Esscher damping φ and nonnegative jump magnitude z, z exp(−φz)≤1/φ. Use φz≤exp(φz) and exp(φz) exp(−φz)=1. Together with the quadratic small-jump estimate this controls the truncated Lévy drift correction on large and small jump domains under the usual Lévy truncated-square condition.
-- source:
--   Pinned Real.add_one_le_exp and Real.exp_add, no proof dependency.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_drift_large_uniform (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    z * Real.exp (-φ * z) ≤ 1 / φ := by sorry
