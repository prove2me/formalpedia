-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_pos
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:05.933607+00:00
-- url     : https://prove2.me/theorems/f63fc3a6-a346-4c69-9ce5-0754eb61e8d8
-- title:
--   Timeout Recertification Run: current Rank pos
-- statement:
--   The Timeout Recertification Run construction uses the current Rank pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L179-L198
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L179-L198

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_currentRank_pos

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.currentRank_pos
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    0 < q := by sorry
