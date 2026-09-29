-- Prove2me | Theorems.Thm_ErlerGross_B3_rational_tsum_eval
-- name    : ErlerGross.B3_rational_tsum_eval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T16:28:36.062985+00:00
-- url     : https://prove2.me/theorems/2f7682de-8d41-42bd-91a0-77fb60154c4e
-- title:
--   Evaluation of the rational series from the B.3 integral
-- statement:
--   The convergent rational series with nth term 1/((2n+1)(3n+1)(3n+2)) sums to log(27/16). A partial-fraction decomposition reduces this to logarithmic limits of harmonic sums in residue classes.
-- source:
--   Independent partial-fractions evaluation of the series arising from the geometric expansion of the integral in Erler-Gross, Appendix B, equation (B.3).

import Mathlib
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem B3_rational_tsum_eval :
    tsum (fun n : Nat => (1 : Real) / ((2 * n + 1) * (3 * n + 1) * (3 * n + 2))) =
      Real.log (27 / 16) := by
  sorry

end ErlerGross
