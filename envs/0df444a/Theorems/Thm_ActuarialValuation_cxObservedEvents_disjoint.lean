-- Prove2me | Theorems.Thm_ActuarialValuation_cxObservedEvents_disjoint
-- name    : ActuarialValuation.cxObservedEvents_disjoint
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:12:22.398153+00:00
-- url     : https://prove2.me/theorems/192d6d6b-6466-4e0e-a09e-9898eaafb2d5
-- title:
--   Censored risk sets and event conditional likelihood: cxObservedEvents_disjoint
-- statement:
--   A censored observation must not simultaneously be a failure contribution. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_cxObservedEvents

namespace ActuarialValuation

theorem cxObservedEvents_disjoint {n : ℕ} (fail censored : Finset (Fin n)) : Disjoint (cxObservedEvents fail censored) censored := by sorry

end ActuarialValuation
