-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_small_quadratic
-- name    : AvramDividend.Classical.gaussian_esscher_drift_small_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:17:45.7761+00:00
-- url     : https://prove2.me/theorems/500afdaa-8bc4-48cb-8bfc-768e2d102131
-- title:
--   Quadratic small-jump bound for Esscher drift correction
-- statement:
--   For nonnegative damping φ and jump magnitude z, z(1−exp(−φz)) is bounded above by φz². Apply x+1≤exp(x) to x=−φz, and multiply by nonnegative z. This supplies the quadratic truncated Lévy small-jump Esscher drift bound, a missing integrability ingredient after the accepted compensator envelope.
-- source:
--   Pinned Mathlib Real.add_one_le_exp; no theorem dependency.

import Mathlib

theorem AvramDividend.Classical.gaussian_esscher_drift_small_quadratic (φ z : ℝ) (hφ : 0 ≤ φ) (hz : 0 ≤ z) :
    z - z * Real.exp (-φ * z) ≤ φ * z ^ 2 := by sorry
