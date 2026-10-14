-- Prove2me | Theorems.Thm_ActuarialValuation_cxEventShare_le_one
-- name    : ActuarialValuation.cxEventShare_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:10:42.382289+00:00
-- url     : https://prove2.me/theorems/4b25c234-124d-4a86-a580-2be6f0bcfda7
-- title:
--   Censored risk sets and event conditional likelihood: cxEventShare_le_one
-- statement:
--   An observed failure's conditional share is at most one when it is included in the risk set. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_cxEventShare

namespace ActuarialValuation

theorem cxEventShare_le_one {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) (i : Fin n) (hi : i∈risk) : cxEventShare beta risk z i≤1 := by sorry

end ActuarialValuation
