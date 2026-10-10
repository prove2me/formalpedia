-- Prove2me | Theorems.Thm_ActuarialValuation_poissonCountMass_ratio
-- name    : ActuarialValuation.poissonCountMass_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:55:45.25153+00:00
-- url     : https://prove2.me/theorems/fd0b6412-7735-4924-b55c-80f7b7df1143
-- title:
--   Successive Poisson count coefficients satisfy a factorial ratio
-- statement:
--   The coefficient for one additional claim is related to the preceding coefficient through the factorial recurrence. This real algebra is valid at rate zero and requires no appeal to an infinite probability-sum calculation.
--
--   **Mathematical statement**
--
--   $$
--   (n+1)p_\lambda(n+1)=\lambda p_\lambda(n)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonCountMass

namespace ActuarialValuation

theorem poissonCountMass_ratio (rate : ℝ) (n : ℕ) :
  (n + 1 : ℝ) * poissonCountMass rate (n + 1) =
    rate * poissonCountMass rate n := by sorry

end ActuarialValuation
