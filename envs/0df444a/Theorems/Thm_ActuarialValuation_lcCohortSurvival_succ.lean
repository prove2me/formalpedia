-- Prove2me | Theorems.Thm_ActuarialValuation_lcCohortSurvival_succ
-- name    : ActuarialValuation.lcCohortSurvival_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:56:27.299063+00:00
-- url     : https://prove2.me/theorems/346dc11a-772a-4c46-b342-6acb78a7ed9d
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortSurvival_succ
-- statement:
--   One further age-calendar year adds its own conditional survival probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   {}_{n+1}p_x={}_np_x(1-q_{n})
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

namespace ActuarialValuation

theorem lcCohortSurvival_succ (q : ℕ → ℝ) (n : ℕ) : lcCohortSurvival q (n+1) = lcCohortSurvival q n * (1-q n) := by sorry

end ActuarialValuation
