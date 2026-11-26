-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_card_timeoutShellBad_sharp_le
-- name    : FirstPassageLinearTransport.exists_card_timeoutShellBad_sharp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:49.151419+00:00
-- url     : https://prove2.me/theorems/258fdaa2-c813-5424-aac8-0a973998c433
-- title:
--   First Passage Linear Transport: exists card timeout Shell Bad sharp le
-- statement:
--   Sharp probability estimate for the literal timeout set.  The hypotheses
--   are only the moving-ratio range and the explicit startup ensuring that the
--   `O(1/L)` threshold loss stays inside the fixed endpoint window.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L926-L1027
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L926-L1027

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.exists_card_timeoutShellBad_sharp_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ K₀ : ℝ, ∀ L m : ℕ,
        0 ≤ K₀ → 0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) := by sorry
