-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentVariance_one
-- name    : ActuarialValuation.siIndependentVariance_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:07:13.218385+00:00
-- url     : https://prove2.me/theorems/faac2626-935d-4843-9d41-53c687991a56
-- title:
--   Independent annual returns on actual product scenarios: siIndependentVariance_one
-- statement:
--   One-year gross-return variance is its second moment less squared mean. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem siIndependentVariance_one (m s : ℝ) : siIndependentVariance m s 1=s-m^2 := by sorry

end ActuarialValuation
