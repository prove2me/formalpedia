-- Prove2me | Theorems.Thm_ErlerGross_B3_digamma_triplication_formula
-- name    : ErlerGross.B3_digamma_triplication_formula
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T12:51:54.290802+00:00
-- url     : https://prove2.me/theorems/61b9f6dc-e403-4563-a79a-fdd389db5fab
-- title:
--   Gauss triplication formula for the digamma function
-- statement:
--   For every complex number z with positive real part,\n\n$$\\psi(z)+\\psi(z+1/3)+\\psi(z+2/3)=3\\psi(3z)-3\\log 3. $$\n\nThis is the logarithmic derivative form of Gauss multiplication at order three.
-- source:
--   Gauss multiplication formula (triplication) for the Gamma function, differentiated logarithmically.

import Mathlib

namespace ErlerGross

theorem B3_digamma_triplication_formula (z : Complex) (hz : 0 < z.re) :
    Complex.digamma z + Complex.digamma (z + (1 : Complex) / 3) +
      Complex.digamma (z + (2 : Complex) / 3) =
        3 * Complex.digamma (3 * z) - 3 * (Real.log 3 : Complex) := by
  sorry

end ErlerGross
