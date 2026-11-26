-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_toMixed
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.toMixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:20.493447+00:00
-- url     : https://prove2.me/theorems/70ea36d8-b573-4081-b52d-babc5f3eeb1d
-- title:
--   Shrinking Recertification Run: to Mixed
-- statement:
--   Forgetting the tolerance schedule retains the exact common-loss chain.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L158-L172
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L158-L172

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.toMixed
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    MixedRecertificationRun P.rStar n elapsed q := by sorry
