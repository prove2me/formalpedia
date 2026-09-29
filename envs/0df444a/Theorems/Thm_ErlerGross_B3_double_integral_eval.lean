-- Prove2me | Theorems.Thm_ErlerGross_B3_double_integral_eval
-- name    : ErlerGross.B3_double_integral_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T13:11:26.074027+00:00
-- url     : https://prove2.me/theorems/26e31195-0f58-473e-a5b2-5f3f28e4d7ca
-- title:
--   Evaluation of the B.3 double integral
-- statement:
--   The double integral over the unit square of $(1-y)/(1-x^2y^3)$ evaluates to $\ln(27/16)$. The integrand can be assigned any value at the corner where its displayed denominator vanishes.
-- source:
--   Independent integral evaluation associated with Erler and Gross, Appendix B, equation (B.3).

import Mathlib
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem B3_double_integral_eval :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      (1 - y) / (1 - x ^ 2 * y ^ 3)) = Real.log (27 / 16) := by
  sorry

end ErlerGross
