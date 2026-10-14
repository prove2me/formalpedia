-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentTwoSecond_factor
-- name    : ActuarialValuation.siIndependentTwoSecond_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:06:34.767018+00:00
-- url     : https://prove2.me/theorems/299879bf-807d-407c-b4c9-bdb003789856
-- title:
--   Independent annual returns on actual product scenarios: siIndependentTwoSecond_factor
-- statement:
--   Independent annual returns give second-moment product factorization without assuming the conclusion. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siGrossSecond
import Definitions.Def_actuarial_siIndependentTwoSecond

namespace ActuarialValuation

theorem siIndependentTwoSecond_factor {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoSecond p q r s=siGrossSecond p r*siGrossSecond q s := by sorry

end ActuarialValuation
