-- Prove2me | Theorems.Thm_ActuarialValuation_lcRateRatio_compose
-- name    : ActuarialValuation.lcRateRatio_compose
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:43:50.987025+00:00
-- url     : https://prove2.me/theorems/3db2987e-7ebe-4019-870a-c32a78e2730a
-- title:
--   Mortality rate ratios and force-to-probability conversion: lcRateRatio_compose
-- statement:
--   Multiplicative mortality ratios compose across successive projection periods. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_{1,3}=R_{1,2}R_{2,3}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRateRatio

namespace ActuarialValuation

theorem lcRateRatio_compose (b k1 k2 k3 : ℝ) : lcRateRatio b k1 k3 = lcRateRatio b k1 k2 * lcRateRatio b k2 k3 := by sorry

end ActuarialValuation
