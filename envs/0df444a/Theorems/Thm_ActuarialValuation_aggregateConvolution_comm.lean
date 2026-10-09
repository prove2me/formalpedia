-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_comm
-- name    : ActuarialValuation.aggregateConvolution_comm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:28:59.873878+00:00
-- url     : https://prove2.me/theorems/36e85377-e084-4c83-9ca2-afa52c7fe4e0
-- title:
--   Order of independent portfolios does not affect aggregate distribution
-- statement:
--   The possible decompositions of a total integer loss s into two nonnegative parts are symmetric. Reindexing k by s-k proves commutativity of discrete convolution, without requiring probability normalisation or any independence hypothesis inside the algebraic definition.
--
--   **Mathematical statement**
--
--   $$
--   (f*g)(s)=(g*f)(s)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_comm (f g : ℕ → ℝ) (s : ℕ) :
  aggregateConvolution f g s = aggregateConvolution g f s := by sorry

end ActuarialValuation
