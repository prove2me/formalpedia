-- Prove2me | Theorems.Thm_ActuarialValuation_lcCohortLives_nonneg
-- name    : ActuarialValuation.lcCohortLives_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:02:07.999586+00:00
-- url     : https://prove2.me/theorems/d9bd0bcd-2b21-4dbe-9374-34e740fda839
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortLives_nonneg
-- statement:
--   Expected survivor counts are nonnegative under nonnegative initial lives and survival. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_0,S_n\ge0\Rightarrow l_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival
import Definitions.Def_actuarial_lcCohortLives

namespace ActuarialValuation

theorem lcCohortLives_nonneg (initial : ℝ) (q : ℕ → ℝ) (n : ℕ) (hi : 0 ≤ initial) (hq : 0 ≤ lcCohortSurvival q n) : 0 ≤ lcCohortLives initial q n := by sorry

end ActuarialValuation
