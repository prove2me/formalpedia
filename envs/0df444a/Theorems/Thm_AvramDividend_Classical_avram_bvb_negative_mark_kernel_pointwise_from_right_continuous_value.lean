-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
-- name    : AvramDividend.Classical.avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:49:32.036569+00:00
-- url     : https://prove2.me/theorems/f2b6f30a-1386-4a95-b455-7b42259d039a
-- title:
--   Right-hand continuity of a reward plus vanishing negative-side reward gives negative-mark kernel pointwise limit
-- statement:
--   For any reward continuous from the nonnegative side at zero and identically zero below zero, any nonnegative sequence tending to zero and any fixed negative jump mark z, the negative mark kernel w(y_n+z)-w(y_n) tends to w(z)-w(0). This is the pointwise dominated-convergence ingredient of the original BV finite-activity negative-mark kernel at zero, without incorrectly assuming two-sided continuity of w.
-- source:
--   Use one-sided continuity along the nonnegative sequence and eventual negativity of y_n+z. The reward is zero to the left and no assumption of continuity at zero from below is made.

import Mathlib
open Filter Set
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
    (w : ℝ → ℝ) (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 (0 : ℝ)))
    (hyPos : ∀ n, 0 ≤ y n)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ z : ℝ, z < 0 → w z = 0)
    (z : ℝ) (hz : z < 0) :
    Tendsto (fun n => w (y n + z) - w (y n))
      atTop (𝓝 (w z - w 0)) := by sorry
