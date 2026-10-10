-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_delta_left
-- name    : ActuarialValuation.aggregateConvolution_delta_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:26:32.335164+00:00
-- url     : https://prove2.me/theorems/10000678-16f3-4d69-8707-fcd0c4848984
-- title:
--   Zero-loss point mass is a left identity for convolution
-- statement:
--   An independent portfolio that always pays zero does not change the distribution of the other portfolio. The convolution sum collapses to the split k=0 and returns f evaluated at the original aggregate loss s.
--
--   **Mathematical statement**
--
--   $$
--   (\delta_0*f)(s)=f(s)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_delta_left (f : ℕ → ℝ) (s : ℕ) :
  aggregateConvolution (fun k => if k = 0 then 1 else 0) f s =
    f s := by sorry

end ActuarialValuation
