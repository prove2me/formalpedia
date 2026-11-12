-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite72_cap_gap_nonnegative
-- name    : AvramDividend.Classical.avram_gfinite72_cap_gap_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:32:12.682908+00:00
-- url     : https://prove2.me/theorems/ce516526-5e35-4f21-9621-f05f1767475d
-- title:
--   Nonnegative upper-cap corner defect from monotone excess value
-- statement:
--   For a value function w whose excess over the identity is nondecreasing along a cap interval, the cap-corner secant defect (w(b)-w(a))-(b-a) is nonnegative. The lemma is an algebraic component of the original Gaussian finite-cap cash estimates.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_gfinite72_cap_gap_nonnegative
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hmono : MonotoneOn (fun z : ℝ => w z - z) (Icc a b)) :
    0 ≤ (w b - w a) - (b - a) := by
  sorry
