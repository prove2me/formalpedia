-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_timeoutShellBad_ballot_ratio_le
-- name    : FirstPassageLinearTransport.exists_timeoutShellBad_ballot_ratio_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:00.863593+00:00
-- url     : https://prove2.me/theorems/b6dc1ef3-d008-50e0-a05f-548650eee0f6
-- title:
--   First Passage Linear Transport: exists timeout Shell Bad ballot ratio le
-- statement:
--   Exact finite ballot timeout estimate on every low-rank window.  This is
--   the formal shell-level form of the manuscript's `m^{-3/2}` improvement,
--   before absorbing the fixed barrier into the implied constant.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L790-L835
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L790-L835

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.exists_timeoutShellBad_ballot_ratio_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ K₀ C : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 ≤ C → 0 < L → L ≤ m →
        (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          C₀ * (((C * K₀ / 2 + 3) * Real.log 2) + 1) /
              ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(collatzFairTiltRate * (m : ℝ)) +
              collatzTiltLambda * ((C * K₀ / 2 + 3) * Real.log 2)) := by sorry
