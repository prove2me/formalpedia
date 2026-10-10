-- Prove2me | Theorems.Thm_ActuarialValuation_lcRateRatio_inverse
-- name    : ActuarialValuation.lcRateRatio_inverse
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:44:06.365797+00:00
-- url     : https://prove2.me/theorems/c6c661f2-f3e7-4267-a92b-e31ee2c056ea
-- title:
--   Mortality rate ratios and force-to-probability conversion: lcRateRatio_inverse
-- statement:
--   Reversing the index change gives an inverse mortality rate multiplier. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R_{12}R_{21}=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRateRatio

namespace ActuarialValuation

theorem lcRateRatio_inverse (b k1 k2 : ℝ) : lcRateRatio b k1 k2 * lcRateRatio b k2 k1 = 1 := by sorry

end ActuarialValuation
