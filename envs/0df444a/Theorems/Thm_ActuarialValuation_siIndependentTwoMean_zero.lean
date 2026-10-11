-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentTwoMean_zero
-- name    : ActuarialValuation.siIndependentTwoMean_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:06:47.878717+00:00
-- url     : https://prove2.me/theorems/690e6d8b-8fa0-4693-9791-3b0f5ede6061
-- title:
--   Independent annual returns on actual product scenarios: siIndependentTwoMean_zero
-- statement:
--   Zero rates in both independent years produce certain accumulated one. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siIndependentTwoMean

namespace ActuarialValuation

theorem siIndependentTwoMean_zero {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (h1 : (∑ j : Fin m, p j)=1) (h2 : (∑ j : Fin n, q j)=1) : siIndependentTwoMean p q (fun _ => 0) (fun _ => 0)=1 := by sorry

end ActuarialValuation
