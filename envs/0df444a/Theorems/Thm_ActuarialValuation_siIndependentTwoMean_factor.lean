-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentTwoMean_factor
-- name    : ActuarialValuation.siIndependentTwoMean_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:06:22.102496+00:00
-- url     : https://prove2.me/theorems/078f9803-13ad-4e66-8ac7-e70514da0322
-- title:
--   Independent annual returns on actual product scenarios: siIndependentTwoMean_factor
-- statement:
--   The true joint product probability law yields factorization of independent annual gross returns. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siGrossMean
import Definitions.Def_actuarial_siIndependentTwoMean

namespace ActuarialValuation

theorem siIndependentTwoMean_factor {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoMean p q r s=siGrossMean p r*siGrossMean q s := by sorry

end ActuarialValuation
