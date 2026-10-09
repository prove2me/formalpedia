-- Prove2me | Theorems.Thm_ActuarialValuation_poissonSplitMass_at_zero
-- name    : ActuarialValuation.poissonSplitMass_at_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:24:34.950312+00:00
-- url     : https://prove2.me/theorems/ac72ff05-0652-4a1b-9b98-0fc09e2854bd
-- title:
--   At zero claim frequency every nonzero marked total has zero mass
-- statement:
--   If the original Poisson stream has zero frequency, then no positive number of arrivals is possible. A marked total of a+b greater than zero has an original Poisson count probability of zero, so its entire joint mass vanishes.
--
--   **Mathematical statement**
--
--   $$
--   a+b>0\Rightarrow J_{0,p}(a,b)=0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonSplitJointMass

namespace ActuarialValuation

theorem poissonSplitMass_at_zero (selection : ℝ) (a b : ℕ)
  (h : 0 < a + b) :
  poissonSplitJointMass 0 selection a b = 0 := by sorry

end ActuarialValuation
