-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_card_le
-- name    : FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:09.524089+00:00
-- url     : https://prove2.me/theorems/dae61547-b196-440c-955a-89f405ef01f7
-- title:
--   First Passage Linear Transport: shrinking First Bad Sources At Rank card le
-- statement:
--   Exact rankwise counting bound with the compressed time support exposed.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L69-L95
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingFirstBad.lean#L69-L95

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_card_le
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / P.rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℚ) ≤
      ((shrinkingFeasibleTimes P M S q).card : ℚ) *
        (1 + 3 * (((q + 2 : ℕ) : ℚ) / P.rStar)) *
          (2 : ℚ) ^ M / ((2 ^ q : ℕ) : ℚ) *
        ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℚ) := by sorry
