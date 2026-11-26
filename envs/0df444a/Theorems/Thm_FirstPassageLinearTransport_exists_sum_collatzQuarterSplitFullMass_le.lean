-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFullMass_le
-- name    : FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullMass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:36:31.136813+00:00
-- url     : https://prove2.me/theorems/a8761f56-bbaa-419a-8f83-40f256746ea9
-- title:
--   First Passage Linear Transport: exists sum collatz Quarter Split Full Mass le
-- statement:
--   The literal full-word event inherits the quarter-split
--   `m^(-3/2)` estimate.  Its coordinates are unique; the next timeout layer only
--   has to split the actual parity word and prove event containment.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2510-L2539
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2510-L2539

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzFullThreeBlockMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by sorry
