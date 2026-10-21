-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_quadratic
-- name    : AvramDividend.Classical.gaussian_compensated_jump_quadratic
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T23:10:08.521596+00:00
-- url     : https://prove2.me/theorems/db26ca60-e9fa-4ad6-86aa-f63f7c6e8e61
-- title:
--   Quadratic upper bound for the Esscher negative-jump exponential compensator
-- statement:
--   For nonnegative θ and negative-jump magnitude z, the compensator exp(−θz)−1+θz is no greater than θ²z². The argument derives exp(−u)≤1−u+u² for u≥0 from exp(u)≥1+u and the elementary positive polynomial 1+u³. This supplies the quadratic small-jump envelope required to integrate the shifted Lévy–Khintchine compensator without assuming finite small-jump first moment.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and real polynomial inequalities.

import Mathlib

theorem AvramDividend.Classical.gaussian_compensated_jump_quadratic
    (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    Real.exp (-θ * z) - 1 + θ * z ≤ (θ * z) ^ 2 := by sorry
