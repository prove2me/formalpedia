-- Prove2me | Theorems.Thm_ActuarialValuation_siIndependentMoment_fundamental
-- name    : ActuarialValuation.siIndependentMoment_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:08:14.287039+00:00
-- url     : https://prove2.me/theorems/ddf6c3c6-9a52-4ea7-88b6-202f961ea019
-- title:
--   Independent annual returns on actual product scenarios: siIndependentMoment_fundamental
-- statement:
--   Actual joint product probability laws establish two independent annual accumulation moments. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_siGrossSecond
import Definitions.Def_actuarial_siIndependentTwoMean
import Definitions.Def_actuarial_siIndependentTwoSecond

namespace ActuarialValuation

theorem siIndependentMoment_fundamental {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoMean p q r s=siGrossMean p r*siGrossMean q s ∧ siIndependentTwoSecond p q r s=siGrossSecond p r*siGrossSecond q s := by sorry

end ActuarialValuation
