-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_directFirstPassage
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.directFirstPassage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:07.176434+00:00
-- url     : https://prove2.me/theorems/842e2760-032d-5d26-bf58-be7ad13e54ee
-- title:
--   Shrinking Recertification Run: direct First Passage
-- statement:
--   The Shrinking Recertification Run construction uses the direct First Passage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L174-L178
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L174-L178

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_directFirstPassage

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.directFirstPassage
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    IsFirstPassage (2 ^ q) n elapsed := by sorry
