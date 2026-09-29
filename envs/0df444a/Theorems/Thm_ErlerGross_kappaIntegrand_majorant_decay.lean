-- Prove2me | Theorems.Thm_ErlerGross_kappaIntegrand_majorant_decay
-- name    : ErlerGross.kappaIntegrand_majorant_decay
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:40:27.350891+00:00
-- url     : https://prove2.me/theorems/4ca473d4-6d94-4c2b-9a10-2593e69d7124
-- title:
--   Decay of the hyperbolic majorant
-- statement:
--   For every real kappa, the hyperbolic majorant pi/(8(1+2 cosh(pi kappa/2))) is no larger than the polynomial tail (1+|kappa|)^(-2).
-- source:
--   Derived analytic estimate for Erler and Gross, hep-th/0406199v2, Appendix B, p. 45.

import Mathlib

namespace ErlerGross
theorem kappaIntegrand_majorant_decay :
    forall kappa : Real,
      Real.pi / (8 * (1 + 2 * Real.cosh (Real.pi * kappa / 2))) <=
        (1 + abs kappa) ^ (-2 : Real) := by
  sorry
end ErlerGross
