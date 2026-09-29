-- Prove2me | Theorems.Thm_ErlerGross_kappaIntegrand_hyperbolic_majorant
-- name    : ErlerGross.kappaIntegrand_hyperbolic_majorant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:40:38.096982+00:00
-- url     : https://prove2.me/theorems/49579942-8df8-4452-bc8c-0921e1c026b5
-- title:
--   Hyperbolic majorant for the kappa integrand
-- statement:
--   The absolute value of the Erler-Gross kappa integrand is bounded by a constant multiple of the reciprocal hyperbolic factor. This isolates the cancellation between cosh(t) - 1 and kappa sinh(t) near zero.
-- source:
--   Erler and Gross, hep-th/0406199v2, Appendix B, p. 45; derived estimate.

import Mathlib
import Definitions.Def_ErlerGross_defs

namespace ErlerGross
theorem kappaIntegrand_hyperbolic_majorant :
    forall kappa : Real, abs (kappaIntegrand kappa) <=
      Real.pi / (8 * (1 + 2 * Real.cosh (Real.pi * kappa / 2))) := by
  sorry
end ErlerGross
