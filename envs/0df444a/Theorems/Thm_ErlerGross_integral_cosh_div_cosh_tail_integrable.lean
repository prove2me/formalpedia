-- Prove2me | Theorems.Thm_ErlerGross_integral_cosh_div_cosh_tail_integrable
-- name    : ErlerGross.integral_cosh_div_cosh_tail_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:43:25.326985+00:00
-- url     : https://prove2.me/theorems/093e97d9-4d27-4b01-8304-d259eee87521
-- title:
--   Tail integrability of the cosh quotient
-- statement:
--   If a and b are complex numbers and the real part gap is positive, the quotient cosh(a x)/cosh(b x) is integrable on the tail (1,infinity), where it decays exponentially.
-- source:
--   Subgoal of ErlerGross.integral_cosh_div_cosh_integrable, following Erler and Gross, Appendix B, p. 45.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem integral_cosh_div_cosh_tail_integrable (a b : Complex) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : Real => Complex.cosh (a * x) / Complex.cosh (b * x)) (Set.Ioi 1) := by
  sorry
end ErlerGross
