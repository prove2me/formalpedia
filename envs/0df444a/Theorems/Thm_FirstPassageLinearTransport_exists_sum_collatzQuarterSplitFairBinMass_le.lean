-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_sum_collatzQuarterSplitFairBinMass_le
-- name    : FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFairBinMass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:23.399094+00:00
-- url     : https://prove2.me/theorems/7ce342b8-3c75-598c-9f78-09788c4e79e3
-- title:
--   First Passage Linear Transport: exists sum collatz Quarter Split Fair Bin Mass le
-- statement:
--   The summed three-block estimate in the canonical quarter-scale split.
--   This is the exact finite form of the `m^(-3/2)` prefactor, before proving
--   that every literal surviving word is represented by the three-block event.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2447-L2505
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2447-L2505

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_sum_collatzQuarterSplitFairBinMass_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ m Q : ℕ, ∀ B : ℝ,
        8 ≤ m → 0 ≤ B →
          ∑ q ∈ Finset.range Q,
              collatzThreeBlockFlatMass (1 / 2)
                (collatzBallotOuterLength m)
                (collatzBallotMiddleLength m) B q ≤
            C * (B + 1) / ((m : ℝ) * Real.sqrt m) *
              Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
                collatzTiltLambda * B) := by sorry
