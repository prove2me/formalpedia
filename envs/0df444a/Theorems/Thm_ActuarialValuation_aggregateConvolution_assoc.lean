-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateConvolution_assoc
-- name    : ActuarialValuation.aggregateConvolution_assoc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:30:24.681987+00:00
-- url     : https://prove2.me/theorems/0fc35f86-218e-40e4-a8bc-fd0d86225a3d
-- title:
--   Three independent portfolios aggregate associatively
-- statement:
--   Triple portfolio aggregation counts all ordered triples of nonnegative component losses summing to s. Grouping the first two or last two portfolios does not alter the finite coefficient sum, so the aggregation operation is associative.
--
--   **Mathematical statement**
--
--   $$
--   ((f*g)*h)(s)=(f*(g*h))(s)
--   $$
-- source:
--   R J Verrall (1989), The individual risk model: a compound distribution, Journal of the Institute of Actuaries 116(1), 101–107, https://doi.org/10.1017/S0020268100036465; N De Pril (1989), The Aggregate Claims Distribution in the Individual Model with Arbitrary Positive Claims, ASTIN Bulletin 19(1), 9–24, https://doi.org/10.2143/AST.19.1.2014913; original finite convolution and support formalisation

import Mathlib
import Definitions.Def_actuarial_aggregateConvolution

namespace ActuarialValuation

theorem aggregateConvolution_assoc (f g h : ℕ → ℝ) (s : ℕ) :
  aggregateConvolution (aggregateConvolution f g) h s =
    aggregateConvolution f (aggregateConvolution g h) s := by sorry

end ActuarialValuation
