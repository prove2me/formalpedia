-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_high_or_low
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_high_or_low
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:05.443723+00:00
-- url     : https://prove2.me/theorems/8e4284d0-2b42-4335-871b-c5f69c9cf391
-- title:
--   Timeout Recertification Run: current Rank high or low
-- statement:
--   The final rank of a timeout run was produced either by a certified high
--   block whose parent lies above the switch, or by a timeout block whose parent
--   lies above the terminal rank.  Only the last constructor matters.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L203-L215
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L203-L215

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_high_or_low
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    (∃ m : ℕ, S ≤ m ∧ q = rationalTargetRank P.rHi m) ∨
      (∃ m : ℕ, L ≤ m ∧ q = timeoutTargetRank K₀ L m) := by sorry
