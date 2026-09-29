-- Prove2me | Theorems.Thm_ErlerGross_B3_digamma_values
-- name    : ErlerGross.B3_digamma_values
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T12:31:37.654297+00:00
-- url     : https://prove2.me/theorems/914407f2-901f-4cfb-b8c0-3f546e192f62
-- title:
--   Digamma values at one-third and one-half
-- statement:
--   The Gauss digamma values at $1/3$, $2/3$, and $1/2$ imply $$\frac{1}{2}\psi(2/3)+\frac{1}{2}\psi(1/3)-\psi(1/2)=-\frac{1}{2}\log(27/16).$$
-- source:
--   Gauss digamma formula at rational arguments (the values at 1/3, 2/3, and 1/2), equivalently derived from the digamma reflection and multiplication formulas.

import Mathlib

namespace ErlerGross

theorem B3_digamma_values :
    Complex.digamma ((2 : ℂ) / 3) / 2 + Complex.digamma ((1 : ℂ) / 3) / 2 -
      Complex.digamma ((1 : ℂ) / 2) = ((-Real.log (27 / 16) / 2 : ℝ) : ℂ) := by
  sorry

end ErlerGross
