-- Prove2me | Theorems.Thm_ErlerGross_integral_cosh_div_cosh_near_zero_integrable
-- name    : ErlerGross.integral_cosh_div_cosh_near_zero_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:43:23.944143+00:00
-- url     : https://prove2.me/theorems/a5806531-1ecc-4a01-809c-37c07c0cba39
-- title:
--   Local integrability of the cosh quotient
-- statement:
--   If a and b are complex numbers and the real part of b is strictly larger than the absolute value of the real part of a, then the quotient cosh(a x)/cosh(b x) is integrable on the bounded interval (0,1).
-- source:
--   Subgoal of ErlerGross.integral_cosh_div_cosh_integrable, following Erler and Gross, Appendix B, p. 45.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem integral_cosh_div_cosh_near_zero_integrable (a b : Complex) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : Real => Complex.cosh (a * x) / Complex.cosh (b * x)) (Set.Ioo 0 1) := by
  sorry
end ErlerGross
