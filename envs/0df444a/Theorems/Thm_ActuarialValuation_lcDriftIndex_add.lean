-- Prove2me | Theorems.Thm_ActuarialValuation_lcDriftIndex_add
-- name    : ActuarialValuation.lcDriftIndex_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T09:31:12.117861+00:00
-- url     : https://prove2.me/theorems/191c0d3f-b0e0-44e1-bbeb-bff5a23c945d
-- title:
--   Age-period Lee-Carter log mortality and drift: lcDriftIndex_add
-- statement:
--   Two successive projections reconcile to a single total period projection. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \kappa_{t+m+n}=\kappa_{t+m}+n\delta
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 659. Ronald D. Lee and Lawrence R. Carter, Modeling and Forecasting U.S. Mortality, Journal of the American Statistical Association 87 (1992), pp. 659–671, https://doi.org/10.1080/01621459.1992.10475265; U.S. Social Security Administration, Out-of-Sample Performance of Stochastic Methods in Forecasting Age-Specific Mortality Rates (2008), https://www.ssa.gov/policy/docs/workingpapers/wp111.html. Parent topic: Age-period Lee-Carter mortality surface, log-linear mortality rate ratios, finite deterministic projection and cohort survival valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1080/01621459.1992.10475265

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcDriftIndex

namespace ActuarialValuation

theorem lcDriftIndex_add (initial drift : ℝ) (m n : ℕ) : lcDriftIndex initial drift (m+n) = lcDriftIndex (lcDriftIndex initial drift m) drift n := by sorry

end ActuarialValuation
