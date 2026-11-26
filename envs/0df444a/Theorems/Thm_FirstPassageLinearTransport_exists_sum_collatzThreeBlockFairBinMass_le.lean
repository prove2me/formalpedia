-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzThreeBlockFairBinMass_le
-- name    : FirstPassageLinearTransport.exists_sum_collatzThreeBlockFairBinMass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:35:54.59363+00:00
-- url     : https://prove2.me/theorems/46cbf042-1ebc-5617-b31d-187677a74b8e
-- title:
--   First Passage Linear Transport: exists sum collatz Three Block Fair Bin Mass le
-- statement:
--   Summation of all terminal bins up to an arbitrary finite cutoff.  The
--   constant is independent of that cutoff.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2289-L2364
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2289-L2364

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_sum_collatzThreeBlockFairBinMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b Q : ℕ, ∀ B : ℝ,
        0 < a → 0 < b → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2) a b B q ≤
            C * (B + 1) /
                (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
              Real.exp (-(collatzFairTiltRate *
                ((2 * a + b : ℕ) : ℝ)) + collatzTiltLambda * B) := by sorry
