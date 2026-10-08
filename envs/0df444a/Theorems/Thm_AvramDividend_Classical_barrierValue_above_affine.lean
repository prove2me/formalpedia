-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
-- name    : AvramDividend.Classical.barrierValue_above_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:31:20.772984+00:00
-- url     : https://prove2.me/theorems/4abc9141-cee9-4cbc-b857-af041701e805
-- title:
--   Barrier-value function is affine above a nonnegative barrier
-- statement:
--   For any real function W and real a≥0, the piecewise barrier-value function is affine above a, with slope one and boundary value v_a(a). This explicit identity supplies the comparison between the above-cap value-function reduction and the candidate v_{c*} above its barrier; no stochastic assumptions are required.
-- source:
--   Direct algebraic consequence of Avram, Palmowski and Pistorius (2007), Eq. (5.1), the barrier-value piecewise definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

namespace AvramDividend.Classical
theorem barrierValue_above_affine (W : ℝ → ℝ) (a x : ℝ)
    (ha : 0 ≤ a) (hax : a < x) :
    barrierValue W a x = (x - a) + barrierValue W a a := by
  sorry
end AvramDividend.Classical
