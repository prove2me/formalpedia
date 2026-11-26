-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_toRankTrace
-- name    : FirstPassageLinearTransport.ShrinkingRecertificationRun.toRankTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:04.165204+00:00
-- url     : https://prove2.me/theorems/6a4ba384-8c38-4a7a-a25d-0114296b1e2f
-- title:
--   Shrinking Recertification Run: to Rank Trace
-- statement:
--   The shrinking run retains the old geometric rank/time trace.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L210-L236
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierRun.lean#L210-L236

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.ShrinkingRecertificationRun.toRankTrace
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    TwoRegimeRankTrace (P.rHi : ℝ) (P.rLo : ℝ) S M elapsed q := by sorry
