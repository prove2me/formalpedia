-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
-- name    : AvramDividend.Classical.barrierValue_zero_affine_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:24:56.481882+00:00
-- url     : https://prove2.me/theorems/f9262914-ea46-4333-87e2-0cd1ac57a1bc
-- title:
--   Zero-barrier candidate equals capital plus its boundary value
-- statement:
--   For any real function W and any nonnegative initial reserve x, the zero-barrier candidate value is exactly the initial reserve x plus its value at zero. This follows from the two branches of the definition of barrierValue and requires no stochastic assumptions. In the zero-cap verification argument it matches the above-cap identity and reduces every x≥0 to the boundary value at 0.
-- source:
--   Elementary algebraic consequence of the piecewise barrierValue definition (5.1), Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_zero_affine_nonnegative
    (W : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    barrierValue W 0 x = x + barrierValue W 0 0 := by
  sorry

end AvramDividend.Classical
