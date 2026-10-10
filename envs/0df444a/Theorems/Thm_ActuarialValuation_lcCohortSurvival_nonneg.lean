-- Prove2me | Theorems.Thm_ActuarialValuation_lcCohortSurvival_nonneg
-- name    : ActuarialValuation.lcCohortSurvival_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:56:42.290187+00:00
-- url     : https://prove2.me/theorems/7eab9374-06db-4ee6-85c6-6b8156e8ddbd
-- title:
--   Projected cohort survival and one-period insured loss: lcCohortSurvival_nonneg
-- statement:
--   No annual death probability exceeds one, so the cohort product is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   q_t\le1\Rightarrow S_n\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

namespace ActuarialValuation

theorem lcCohortSurvival_nonneg (q : ℕ → ℝ) (n : ℕ) (hq : ∀ t ∈ Finset.range n, q t ≤ 1) : 0 ≤ lcCohortSurvival q n := by sorry

end ActuarialValuation
