-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentVariance_succ
-- name    : ActuarialValuation.siIndependentVariance_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:07:56.889865+00:00
-- url     : https://prove2.me/theorems/12264536-d0dd-4e1f-b49b-a886af9477b6
-- title:
--   Independent annual returns on actual product scenarios: siIndependentVariance_succ
-- statement:
--   Multi-year variance recursion separates earlier accumulation risk and newest year volatility. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[G_1G_2]=\mathbb{E}[G_1]\mathbb{E}[G_2]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentVariance

namespace ActuarialValuation

theorem siIndependentVariance_succ (m s : ℝ) (n : ℕ) : siIndependentVariance m s (n+1)=s*(siIndependentVariance m s n)+(s-m^2)*(m^n)^2 := by sorry

end ActuarialValuation
