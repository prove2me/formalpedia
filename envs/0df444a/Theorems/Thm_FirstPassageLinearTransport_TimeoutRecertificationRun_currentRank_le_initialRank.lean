-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_le_initialRank
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_le_initialRank
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:00.762883+00:00
-- url     : https://prove2.me/theorems/a56cf180-1600-56fb-87c5-8fc1c09c26c2
-- title:
--   Timeout Recertification Run: current Rank le initial Rank
-- statement:
--   Every later timeout-run rank lies below the rank reached by the initial
--   high block.  This is the rank interface used to keep all post-initial
--   certified blocks below the original scale.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L252-L262
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L252-L262

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_le_initialRank
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    q ≤ rationalTargetRank P.rHi M := by sorry
