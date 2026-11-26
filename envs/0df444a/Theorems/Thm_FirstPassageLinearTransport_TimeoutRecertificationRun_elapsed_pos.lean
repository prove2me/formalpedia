-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_elapsed_pos
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.elapsed_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:59.923163+00:00
-- url     : https://prove2.me/theorems/15e4dda7-c316-4a08-86cf-82f76e88e16d
-- title:
--   Timeout Recertification Run: elapsed pos
-- statement:
--   The Timeout Recertification Run construction uses the elapsed pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L164-L177
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L164-L177

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_pos

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.elapsed_pos
    {P : TimeoutHighRunData} {K₀ : ℝ} {L M S n elapsed q : ℕ}
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    0 < elapsed := by sorry
