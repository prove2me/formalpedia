-- Prove2me | solution 1 for rademacher_two_point_l4_l2_bonami_base
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T02:34:24.719192+00:00
-- url     : https://prove2.me/submissions/756fd7a5-4c4b-49ad-9951-8fcfbb15121f

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem solution (a b : ℝ) :
    (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      ≤ ((((a + Real.sqrt 3 * b) ^ 2 + (a - Real.sqrt 3 * b) ^ 2) / 2)) ^ 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrhs : (((a + Real.sqrt 3 * b) ^ 2 + (a - Real.sqrt 3 * b) ^ 2) / 2)
      = a ^ 2 + 3 * b ^ 2 := by
    have : (a + Real.sqrt 3 * b) ^ 2 + (a - Real.sqrt 3 * b) ^ 2
        = 2 * a ^ 2 + 2 * (Real.sqrt 3 ^ 2) * b ^ 2 := by ring
    rw [this, h3]; ring
  have hlhs : (((a + b) ^ 4 + (a - b) ^ 4) / 2)
      = a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 := by ring
  rw [hlhs, hrhs]
  nlinarith [sq_nonneg (b ^ 2), sq_nonneg a, sq_nonneg b]
