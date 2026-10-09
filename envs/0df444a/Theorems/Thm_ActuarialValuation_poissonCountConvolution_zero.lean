-- Prove2me | Theorems.Thm_ActuarialValuation_poissonCountConvolution_zero
-- name    : ActuarialValuation.poissonCountConvolution_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:01:17.828986+00:00
-- url     : https://prove2.me/theorems/788003fc-7bb6-4ee8-beff-dc8132fa44bb
-- title:
--   No arrivals in the combined process requires zero in each component
-- statement:
--   When the combined count is zero, the finite allocation sum has one term, corresponding to zero arrivals in both streams. This provides a base case for the more substantial Poisson superposition identity.
--
--   **Mathematical statement**
--
--   $$
--   h_0=p_a(0)p_b(0)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountConvolution
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonCountConvolution_zero (a b : ℝ) :
  poissonCountConvolution a b 0 =
    poissonCountMass a 0 * poissonCountMass b 0 := by sorry

end ActuarialValuation
