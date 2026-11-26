-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzLowerSurvivalMass_le
-- name    : FirstPassageLinearTransport.collatzLowerSurvivalMass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:33:26.179033+00:00
-- url     : https://prove2.me/theorems/7a865fed-2906-56f7-b1d3-d4db448ae207
-- title:
--   First Passage Linear Transport: collatz Lower Survival Mass le
-- statement:
--   Appendix B.1 specialized to the critical Collatz tilt.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1130-L1136
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1130-L1136

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzLowerSurvivalMass_le
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt collatzLogIncrement (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by sorry
