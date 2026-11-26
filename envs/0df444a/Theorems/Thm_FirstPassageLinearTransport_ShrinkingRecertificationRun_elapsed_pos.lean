-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_pos
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:26.423537+00:00
-- url     : https://prove2.me/theorems/32ea0465-5e76-52d1-8b0a-d24e648e1c86
-- title:
--   Shrinking Recertification Run: elapsed pos
-- statement:
--   The Shrinking Recertification Run construction uses the elapsed pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L118-L131
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L118-L131

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_elapsed_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_pos
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    0 < elapsed := by sorry
