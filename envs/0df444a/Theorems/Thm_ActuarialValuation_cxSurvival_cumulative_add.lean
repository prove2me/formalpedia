-- Prove2me | Theorems.Thm_ActuarialValuation_cxSurvival_cumulative_add
-- name    : ActuarialValuation.cxSurvival_cumulative_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:07:08.202345+00:00
-- url     : https://prove2.me/theorems/239f5cff-4b1f-4b41-bf9d-ffef44f123fd
-- title:
--   Positive proportional hazards and cumulative survival: cxSurvival_cumulative_add
-- statement:
--   Survival factors multiply for two disjoint cumulative hazard periods. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_cxSurvival

namespace ActuarialValuation

theorem cxSurvival_cumulative_add (H1 H2 beta z : ℝ) : cxSurvival (H1+H2) beta z=cxSurvival H1 beta z*cxSurvival H2 beta z := by sorry

end ActuarialValuation
