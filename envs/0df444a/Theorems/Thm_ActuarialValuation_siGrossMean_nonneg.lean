-- Prove2me | Theorems.Thm_ActuarialValuation_siGrossMean_nonneg
-- name    : ActuarialValuation.siGrossMean_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:05:52.244801+00:00
-- url     : https://prove2.me/theorems/9115bc55-07ad-437f-8718-b29045615279
-- title:
--   Independent annual returns on actual product scenarios: siGrossMean_nonneg
-- statement:
--   A nonnegative gross return under nonnegative probabilities has nonnegative expectation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

theorem siGrossMean_nonneg {m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (hp : ∀ j, 0≤p j) (hr : ∀ j, -1≤r j) : 0≤siGrossMean p r := by sorry

end ActuarialValuation
