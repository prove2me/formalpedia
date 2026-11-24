-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_joint_error_bound
-- name    : Formalism.LFunctionChainParameters.LErr.joint_error_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:58.885422+00:00
-- url     : https://prove2.me/theorems/914537b6-9694-44bc-8b8b-1f9a65a49bbf
-- title:
--   LErr: joint error bound
-- statement:
--   The LErr construction uses the joint error bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L588-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L588-L606

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

theorem Formalism.LFunctionChainParameters.LErr.joint_error_bound {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    LeadingTermGrowthJoint (H := H) := by sorry
