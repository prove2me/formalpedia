-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_delta_right
-- name    : ActuarialValuation.aggregateConvolution_delta_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:27:22.219742+00:00
-- url     : https://prove2.me/theorems/49ce2513-f816-45fa-8fb9-edf8452efd27
-- title:
--   Zero-loss point mass is a right identity
-- statement:
--   Combining a nontrivial claim portfolio with another portfolio that pays exactly zero preserves every aggregate probability coefficient. The only surviving split assigns all loss to the first component.
--
--   **Mathematical statement**
--
--   $$
--   (f*\delta_0)(s)=f(s)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_delta_right (f : ℕ → ℝ) (s : ℕ) :
  aggregateConvolution f (fun k => if k = 0 then 1 else 0) s =
    f s := by sorry

end ActuarialValuation
