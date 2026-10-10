-- Prove2me | Theorems.Thm_ActuarialValuation_poissonCountMass_zero
-- name    : ActuarialValuation.poissonCountMass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:54:08.43246+00:00
-- url     : https://prove2.me/theorems/1861a587-541d-4b7c-a030-6c8c87c130f5
-- title:
--   Zero claims have exponential probability
-- statement:
--   The factorial at zero and every real rate raised to zero both equal one. Consequently the no-claim count coefficient is the exponential of the negative claim frequency, including the zero-frequency boundary.
--
--   **Mathematical statement**
--
--   $$
--   p_\lambda(0)=e^{-\lambda}
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonCountMass_zero (rate : ℝ) :
  poissonCountMass rate 0 = Real.exp (-rate) := by sorry

end ActuarialValuation
