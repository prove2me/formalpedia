-- Prove2me | Theorems.Thm_ActuarialValuation_lcCohortSurvival_le_one
-- name    : ActuarialValuation.lcCohortSurvival_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:56:55.41577+00:00
-- url     : https://prove2.me/theorems/90dbb8d6-1403-4910-9150-c86ff4667487
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortSurvival_le_one
-- statement:
--   Multiplying valid annual survival probabilities cannot increase cohort survival above one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le q_t\le1\Rightarrow S_n\le1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

namespace ActuarialValuation

theorem lcCohortSurvival_le_one (q : ℕ → ℝ) (n : ℕ) (hq : ∀ t ∈ Finset.range n, 0 ≤ q t ∧ q t ≤ 1) : lcCohortSurvival q n ≤ 1 := by sorry

end ActuarialValuation
