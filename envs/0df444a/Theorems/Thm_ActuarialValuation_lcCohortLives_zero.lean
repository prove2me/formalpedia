-- Prove2me | Theorems.Thm_ActuarialValuation_lcCohortLives_zero
-- name    : ActuarialValuation.lcCohortLives_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:01:09.846576+00:00
-- url     : https://prove2.me/theorems/e15d3da8-4023-46b9-93cd-b58a72499c61
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortLives_zero
-- statement:
--   Expected cohort starting lives reproduce the starting number exposed. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_0=l_0S_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortLives

namespace ActuarialValuation

theorem lcCohortLives_zero (initial : ℝ) (q : ℕ → ℝ) : lcCohortLives initial q 0 = initial := by sorry

end ActuarialValuation
