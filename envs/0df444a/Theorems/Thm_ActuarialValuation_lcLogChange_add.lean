-- Prove2me | Theorems.Thm_ActuarialValuation_lcLogChange_add
-- name    : ActuarialValuation.lcLogChange_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:37:55.899434+00:00
-- url     : https://prove2.me/theorems/7f1c93ec-c804-474a-bba6-957939610b79
-- title:
--   Age-period Lee-Carter log mortality and drift: lcLogChange_add
-- statement:
--   Log mortality changes are additive over disjoint periods. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta_{1,3}=\Delta_{1,2}+\Delta_{2,3}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcLogChange

namespace ActuarialValuation

theorem lcLogChange_add (b k1 k2 k3 : ℝ) : lcLogChange b k1 k3 = lcLogChange b k1 k2 + lcLogChange b k2 k3 := by sorry

end ActuarialValuation
