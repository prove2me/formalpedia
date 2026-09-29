-- Prove2me | solution 1 for flt5_rs_eq_c1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-14T17:06:28.070539+00:00
-- url     : https://prove2.me/submissions/bd01e48e-3e5e-411a-b070-8a8b238deced

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_pow5_inj

-- Full proof: r*s = c1 from w*v = c1^5, w = r^5, v = s^5
-- (r*s)^5 = r^5 * s^5 = w * v = c1^5, so r*s = c1 by injectivity of (·)^5
theorem solution (r s c1 w v : ℤ)
    (hwv : w * v = c1 ^ 5) (hr : w = r ^ 5) (hs : v = s ^ 5) :
    r * s = c1 := by
  apply flt5_pow5_inj
  rw [mul_pow, ← hr, ← hs]
  exact hwv
