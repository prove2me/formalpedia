-- Prove2me | Theorems.Thm_ActuarialValuation_lcLogChange_reverse
-- name    : ActuarialValuation.lcLogChange_reverse
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:33:21.007561+00:00
-- url     : https://prove2.me/theorems/2ff5401b-69c4-4550-b80d-1a329fe0a341
-- title:
--   Age-period Lee-Carter log mortality and drift: lcLogChange_reverse
-- statement:
--   Swapping projection endpoints negates log mortality improvement. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta_{1,2}=-\Delta_{2,1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcLogChange

namespace ActuarialValuation

theorem lcLogChange_reverse (b k1 k2 : ℝ) : lcLogChange b k1 k2 = - lcLogChange b k2 k1 := by sorry

end ActuarialValuation
