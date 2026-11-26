-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedTree_upper
-- name    : FirstPassageLinearTransport.stoppedTree_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:15.068932+00:00
-- url     : https://prove2.me/theorems/472d2c72-dbb9-414a-b3c0-d2ad7ff12603
-- title:
--   First Passage Linear Transport: stopped Tree upper
-- statement:
--   Optional-stopping inequality with the exact finite overshoot factor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2968-L3010
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2968-L3010

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedTree_upper
    {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    (2 : ℝ) ^ r ≤
      (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) +
        safeTerminalSum u r 1 := by sorry
