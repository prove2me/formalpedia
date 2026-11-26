-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rationalTargetRank_lt_parent
-- name    : FirstPassageLinearTransport.rationalTargetRank_lt_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:16:24.850095+00:00
-- url     : https://prove2.me/theorems/2c51a9ce-d715-4e14-98d6-79108fe18173
-- title:
--   First Passage Linear Transport: rational Target Rank lt parent
-- statement:
--   The First Passage Linear Transport construction uses the rational Target Rank lt parent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L42-L49
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L42-L49

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.rationalTargetRank_lt_parent
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m : ℕ} (hm : 0 < m) :
    rationalTargetRank r m < m := by sorry
