-- Prove2me | solution 1 for rademacher_two_point_l4_l2_bonami_general_scale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T02:34:25.264129+00:00
-- url     : https://prove2.me/submissions/7a08af75-4828-4424-ba42-fe5dbc1d0d18

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem solution (a b s : ℝ) (hs : 3 ≤ s ^ 2) :
    (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      ≤ ((((a + s * b) ^ 2 + (a - s * b) ^ 2) / 2)) ^ 2 := by
  have hrhs : (((a + s * b) ^ 2 + (a - s * b) ^ 2) / 2)
      = a ^ 2 + s ^ 2 * b ^ 2 := by ring
  have hlhs : (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      = a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 := by ring
  rw [hlhs, hrhs]
  have hs4 : 9 ≤ s ^ 4 := by nlinarith [hs, sq_nonneg (s ^ 2 - 3)]
  have h1 : 6 * (a ^ 2 * b ^ 2) ≤ 2 * s ^ 2 * (a ^ 2 * b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg b), hs]
  have h2 : b ^ 4 ≤ s ^ 4 * b ^ 4 := by
    nlinarith [sq_nonneg (b ^ 2), hs4]
  nlinarith [h1, h2]
