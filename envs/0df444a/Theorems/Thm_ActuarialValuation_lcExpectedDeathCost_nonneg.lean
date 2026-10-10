-- Prove2me | Theorems.Thm_ActuarialValuation_lcExpectedDeathCost_nonneg
-- name    : ActuarialValuation.lcExpectedDeathCost_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:02:57.40628+00:00
-- url     : https://prove2.me/theorems/a3611080-6037-4b88-bac4-5b9788c1c9e6
-- title:
--   Projected cohort survival and one-period insured loss: lcExpectedDeathCost_nonneg
-- statement:
--   A nonnegative death benefit gives nonnegative one-year expected claim cost. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l,q,B\ge0\Rightarrow C\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcExpectedDeathCost

namespace ActuarialValuation

theorem lcExpectedDeathCost_nonneg (lives q b : ℝ) (hl : 0 ≤ lives) (hq : 0 ≤ q) (hb : 0 ≤ b) : 0 ≤ lcExpectedDeathCost lives q b := by sorry

end ActuarialValuation
