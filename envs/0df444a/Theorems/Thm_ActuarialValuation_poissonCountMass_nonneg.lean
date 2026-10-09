-- Prove2me | Theorems.Thm_ActuarialValuation_poissonCountMass_nonneg
-- name    : ActuarialValuation.poissonCountMass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:56:17.716048+00:00
-- url     : https://prove2.me/theorems/5462f017-7085-4a34-87a9-c5569a034b6b
-- title:
--   A nonnegative Poisson rate produces nonnegative count coefficients
-- statement:
--   The exponential factor is positive, the nth power of a nonnegative rate is nonnegative, and the real-cast factorial denominator is strictly positive. Therefore each Poisson count mass is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \lambda\ge0\Rightarrow p_\lambda(n)\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonCountMass_nonneg (rate : ℝ) (n : ℕ)
  (hr : 0 ≤ rate) : 0 ≤ poissonCountMass rate n := by sorry

end ActuarialValuation
