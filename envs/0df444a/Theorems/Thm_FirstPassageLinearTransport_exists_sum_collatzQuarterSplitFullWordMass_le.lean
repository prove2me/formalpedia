-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFullWordMass_le
-- name    : FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullWordMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:33.469606+00:00
-- url     : https://prove2.me/theorems/44ab5877-c18d-41a6-a9b1-661a1c7abd59
-- title:
--   First Passage Linear Transport: exists sum collatz Quarter Split Full Word Mass le
-- statement:
--   Direct full-word form of the quarter-split estimate.  The equivalence
--   above certifies that no word is lost or duplicated by the three-block
--   coordinates.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2544-L2582
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2544-L2582

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFullWordMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzFullWordMass (1 / 2) m B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by sorry
