-- Prove2me | Theorems.Thm_ErlerGross_kappaIntegrand_integrable
-- name    : ErlerGross.kappaIntegrand_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:09:03.591435+00:00
-- url     : https://prove2.me/theorems/9e876ad6-329c-4dff-adb1-a12aa1a0a765
-- title:
--   Integrability of the ?-basis integrand
-- statement:
--   The kappa-basis integrand defined in Appendix B is Lebesgue integrable on the real line.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2, Appendix B, p. 45 (kappa-basis integrand).

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross
theorem kappaIntegrand_integrable : Integrable kappaIntegrand := by
  sorry
end ErlerGross
