-- Prove2me | Theorems.Thm_ActuarialValuation_cxRiskDenom_empty
-- name    : ActuarialValuation.cxRiskDenom_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:07:45.136257+00:00
-- url     : https://prove2.me/theorems/d489acab-94e6-496a-998d-0b503ee255e5
-- title:
--   Censored risk sets and event conditional likelihood: cxRiskDenom_empty
-- statement:
--   An empty at-risk set has zero total risk weight. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   L(\beta)=\prod_{i\in D}\frac{e^{\beta z_i}}{\sum_{j\in R(t_i)}e^{\beta z_j}}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 190. D. R. Cox (1972), Regression Models and Life-Tables, Journal of the Royal Statistical Society B 34:187–202, https://doi.org/10.1111/j.2517-6161.1972.tb00899.x; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, lifetime failure-time models. Parent topic: Multiplicative baseline hazard, finite at-risk sets, partial likelihood, censored selection, score derivatives and survival prediction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.2517-6161.1972.tb00899.x

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom

namespace ActuarialValuation

theorem cxRiskDenom_empty {n : ℕ} (beta : ℝ) (z : Fin n → ℝ) : cxRiskDenom beta ∅ z=0 := by sorry

end ActuarialValuation
