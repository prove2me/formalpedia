-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_targetScale_rat
-- name    : FirstPassageLinearTransport.targetScale_rat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:13.225474+00:00
-- url     : https://prove2.me/theorems/6e94ec2a-30da-5562-a352-b6c361fdd4df
-- title:
--   First Passage Linear Transport: target Scale rat
-- statement:
--   The First Passage Linear Transport construction uses the target Scale rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L26-L27
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean#L26-L27

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.targetScale_rat (r : ℚ) (m : ℕ) :
    targetScale (r : ℝ) m = 2 ^ rationalTargetRank r m := by sorry
