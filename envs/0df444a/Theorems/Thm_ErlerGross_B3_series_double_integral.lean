-- Prove2me | Theorems.Thm_ErlerGross_B3_series_double_integral
-- name    : ErlerGross.B3_series_double_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T13:11:36.048245+00:00
-- url     : https://prove2.me/theorems/8dd69892-56a4-43be-8437-c542b487d12e
-- title:
--   Integral representation of the B.3 series
-- statement:
--   For the sequence of terms in Erler and Gross equation (B.3), its sum is negative one half of a double integral over the unit square with integrand $(1-y)/(1-x^2y^3)$. The geometric series in the denominator gives this integral representation.
-- source:
--   Independent integral method for Erler and Gross, Appendix B, equation (B.3).

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem B3_series_double_integral :
    HasSum (fun n : ℕ => b3Term (n + 1))
      ((-1 / 2) * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1 - y) / (1 - x ^ 2 * y ^ 3))) := by
  sorry

end ErlerGross
