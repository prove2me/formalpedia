-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentVariance_nonneg
-- name    : ActuarialValuation.siIndependentVariance_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:07:26.927979+00:00
-- url     : https://prove2.me/theorems/9c86c4a9-383b-491d-9f04-c11945b9b930
-- title:
--   Independent annual returns on actual product scenarios: siIndependentVariance_nonneg
-- statement:
--   Normalized iid gross return moments produce nonnegative multi-year variance. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem siIndependentVariance_nonneg (m s : ℝ) (hm : 0≤m) (hs : m^2≤s) (n : ℕ) : 0≤siIndependentVariance m s n := by sorry

end ActuarialValuation
