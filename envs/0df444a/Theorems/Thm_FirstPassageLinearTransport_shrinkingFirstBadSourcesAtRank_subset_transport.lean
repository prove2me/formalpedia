-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_subset_transport
-- name    : FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_subset_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:27.623135+00:00
-- url     : https://prove2.me/theorems/69560d85-2528-4417-adaa-2d00d7924dbc
-- title:
--   First Passage Linear Transport: shrinking First Bad Sources At Rank subset transport
-- statement:
--   Every literal failed endpoint lies in the exact support-sensitive direct
--   transport set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L50-L66
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L50-L66

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_subset_transport
    (P : ShrinkingBarrierRunData) {M S q : ℕ} :
    shrinkingFirstBadSourcesAtRank P M S q ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ q)
        (shrinkingFeasibleTimes P M S q)
        (landingBad q (shrinkingTargetTolerance P M S q))
        (((q + 2 : ℕ) : ℚ) / P.rStar) := by sorry
