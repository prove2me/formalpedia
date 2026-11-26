-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzThreeBlockFlatMass_fair_le_tilt
-- name    : FirstPassageLinearTransport.collatzThreeBlockFlatMass_fair_le_tilt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:47.368165+00:00
-- url     : https://prove2.me/theorems/fbefa226-cfa1-4ef5-9e3d-70440a63161e
-- title:
--   First Passage Linear Transport: collatz Three Block Flat Mass fair le tilt
-- statement:
--   The fair mass of a terminal bin is its critical tilted envelope times
--   the exact exponential change-of-weight factor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2220-L2249
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2220-L2249

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzThreeBlockFlatMass_fair_le_tilt
    {a b : ℕ} {B q : ℝ} :
    collatzThreeBlockFlatMass (1 / 2) a b B q ≤
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * (q - B)) *
        collatzThreeBlockFlatMass collatzTilt a b B q := by sorry
