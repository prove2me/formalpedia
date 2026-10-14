-- Prove2me | Theorems.Thm_ActuarialValuation_siGrossSecond_nonneg
-- name    : ActuarialValuation.siGrossSecond_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:06:09.75245+00:00
-- url     : https://prove2.me/theorems/b788ddbb-97cf-4f86-a4b7-fe29671b72b6
-- title:
--   Independent annual returns on actual product scenarios: siGrossSecond_nonneg
-- statement:
--   Second gross return moments are nonnegative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

theorem siGrossSecond_nonneg {m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (hp : ∀ j, 0≤p j) : 0≤siGrossSecond p r := by sorry

end ActuarialValuation
