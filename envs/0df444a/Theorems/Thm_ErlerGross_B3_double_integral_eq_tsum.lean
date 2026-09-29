-- Prove2me | Theorems.Thm_ErlerGross_B3_double_integral_eq_tsum
-- name    : ErlerGross.B3_double_integral_eq_tsum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T16:30:54.648628+00:00
-- url     : https://prove2.me/theorems/345f8e65-3a76-4d3a-b52b-946f6ab7f8a6
-- title:
--   Geometric-series expansion of the B.3 double integral
-- statement:
--   Expanding the nonnegative integrand by the geometric series and integrating each monomial gives this representation of the double integral as a convergent rational series.
-- source:
--   Direct geometric-series and monotone-convergence argument for the unit-square integral in Erler-Gross, Appendix B, equation (B.3).

import Mathlib
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem B3_double_integral_eq_tsum :
    intervalIntegral (fun x : Real =>
      intervalIntegral (fun y : Real => (1 - y) / (1 - x ^ 2 * y ^ 3)) 0 1 volume) 0 1 volume =
      tsum (fun n : Nat => (1 : Real) / ((2 * n + 1) * (3 * n + 1) * (3 * n + 2))) := by
  sorry

end ErlerGross
