-- Prove2me | Theorems.Thm_ActuarialValuation_cxHazard_zero
-- name    : ActuarialValuation.cxHazard_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:04:47.150496+00:00
-- url     : https://prove2.me/theorems/921f5a8d-5621-4c29-9e21-a912e02f4237
-- title:
--   Positive proportional hazards and cumulative survival: cxHazard_zero
-- statement:
--   No baseline hazard produces no event intensity. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \lambda(t\mid z)=\lambda_0(t)e^{\beta z},\quad S(t\mid z)=e^{-\Lambda_0(t)e^{\beta z}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 190. D. R. Cox (1972), Regression Models and Life-Tables, Journal of the Royal Statistical Society B 34:187–202, https://doi.org/10.1111/j.2517-6161.1972.tb00899.x; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, lifetime failure-time models. Parent topic: Multiplicative baseline hazard, finite at-risk sets, partial likelihood, censored selection, score derivatives and survival prediction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.2517-6161.1972.tb00899.x

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxHazard

namespace ActuarialValuation

theorem cxHazard_zero (beta z : ℝ) : cxHazard 0 beta z=0 := by sorry

end ActuarialValuation
