-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_elapsed_le_horizon
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_le_horizon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:10.374352+00:00
-- url     : https://prove2.me/theorems/6c9de8cf-6b43-4a7e-a460-0e18fde6c636
-- title:
--   Shrinking Recertification Run: elapsed le horizon
-- statement:
--   The Shrinking Recertification Run construction uses the elapsed le horizon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L238-L245
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L238-L245

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.elapsed_le_horizon
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    elapsed ≤ twoRegimeHorizon P.rHi P.rLo S M := by sorry
