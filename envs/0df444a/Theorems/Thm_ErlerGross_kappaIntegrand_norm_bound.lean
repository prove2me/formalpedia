-- Prove2me | Theorems.Thm_ErlerGross_kappaIntegrand_norm_bound
-- name    : ErlerGross.kappaIntegrand_norm_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:24:02.091435+00:00
-- url     : https://prove2.me/theorems/508e2426-ef0c-4906-ab0c-f98c55e6eeb5
-- title:
--   A polynomial majorant for the kappa-basis integrand
-- statement:
--   For every real kappa, the absolute value of the kappa-basis integrand is at most (1 + |kappa|)^(-2). This gives an integrable majorant on the real line.
-- source:
--   Derived analytic estimate for the integrand in Erler and Gross, hep-th/0406199v2, Appendix B, p. 45.

import Mathlib
import Definitions.Def_ErlerGross_defs

namespace ErlerGross
theorem kappaIntegrand_norm_bound :
    forall kappa : Real, abs (kappaIntegrand kappa) <= (1 + abs kappa) ^ (-2 : Real) := by
  sorry
end ErlerGross
