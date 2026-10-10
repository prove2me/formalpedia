-- Prove2me | Theorems.Thm_ActuarialValuation_lcLeeCarterCohort_fundamental
-- name    : ActuarialValuation.lcLeeCarterCohort_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:03:37.264981+00:00
-- url     : https://prove2.me/theorems/966ba589-6170-4a94-9f61-29bc96ba73e0
-- title:
--   Projected cohort survival and one-period insured loss: lcLeeCarterCohort_fundamental
-- statement:
--   The comprehensive mortality capstone links Lee-Carter rate ratios with a valid bounded cohort survival law and the nonnegative one-year insured death outgo. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   m_{x,2}=m_{x,1}R,\;m_{x,2}>0,\;0\le S_{n+1}\le S_n,\;E[C]\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRate
import Definitions.Def_actuarial_lcRateRatio
import Definitions.Def_actuarial_lcCohortSurvival
import Definitions.Def_actuarial_lcCohortLives
import Definitions.Def_actuarial_lcExpectedDeathCost

namespace ActuarialValuation

theorem lcLeeCarterCohort_fundamental (a b k1 k2 initial benefit : ℝ) (q : ℕ → ℝ) (n : ℕ) (hi : 0 ≤ initial) (hb : 0 ≤ benefit) (hq : ∀ t ∈ Finset.range (n+1), 0 ≤ q t ∧ q t ≤ 1) : (lcRate a b k2 = lcRate a b k1 * lcRateRatio b k1 k2) ∧ (0 < lcRate a b k2) ∧ (0 ≤ lcCohortSurvival q (n+1)) ∧ (lcCohortSurvival q (n+1) ≤ lcCohortSurvival q n) ∧ (0 ≤ lcExpectedDeathCost (lcCohortLives initial q n) (q n) benefit) := by sorry

end ActuarialValuation
