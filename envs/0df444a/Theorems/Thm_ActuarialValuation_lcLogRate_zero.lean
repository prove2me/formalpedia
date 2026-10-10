-- Prove2me | Theorems.Thm_ActuarialValuation_lcLogRate_zero
-- name    : ActuarialValuation.lcLogRate_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:29:30.950106+00:00
-- url     : https://prove2.me/theorems/06c3a72f-dca2-44cd-a59c-bede861b098d
-- title:
--   Age-period Lee-Carter log mortality and drift: lcLogRate_zero
-- statement:
--   Zero mortality index gives age-specific baseline log-rate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \kappa=0\Rightarrow\log m=a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcLogRate

namespace ActuarialValuation

theorem lcLogRate_zero (a b : ℝ) : lcLogRate a b 0 = a := by sorry

end ActuarialValuation
