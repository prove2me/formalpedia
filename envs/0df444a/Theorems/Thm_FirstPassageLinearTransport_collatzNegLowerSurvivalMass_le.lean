-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzNegLowerSurvivalMass_le
-- name    : FirstPassageLinearTransport.collatzNegLowerSurvivalMass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:33:27.209015+00:00
-- url     : https://prove2.me/theorems/0aa1b91c-fe5a-5a6d-81e8-6ef4e218a5f7
-- title:
--   First Passage Linear Transport: collatz Neg Lower Survival Mass le
-- statement:
--   The same survival estimate for the reversed-negated terminal block.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1139-L1154
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1139-L1154

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzNegLowerSurvivalMass_le
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass collatzTilt
        (fun b ↦ -collatzLogIncrement b) (-B) n 0 ≤
      (1 + 2 / collatzTiltVariance) * (B + 1) / Real.sqrt n := by sorry
