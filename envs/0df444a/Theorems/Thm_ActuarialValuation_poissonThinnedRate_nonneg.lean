-- Prove2me | Theorems.Thm_ActuarialValuation_poissonThinnedRate_nonneg
-- name    : ActuarialValuation.poissonThinnedRate_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:56:51.324984+00:00
-- url     : https://prove2.me/theorems/3f0fc229-fd8b-4ce5-a842-f34f0aa32752
-- title:
--   Thinning a valid stream yields nonnegative frequency
-- statement:
--   A nonnegative claim frequency multiplied by a nonnegative marking probability yields a nonnegative selected frequency. The usual restriction selection≤1 is required for a full probability model but not for this sign identity.
--
--   **Mathematical statement**
--
--   $$
--   \lambda,p\ge0\Rightarrow\lambda p\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib
import Definitions.Def_actuarial_poissonThinnedRate

namespace ActuarialValuation

theorem poissonThinnedRate_nonneg (rate selection : ℝ)
  (hr : 0 ≤ rate) (hp : 0 ≤ selection) :
  0 ≤ poissonThinnedRate rate selection := by sorry

end ActuarialValuation
