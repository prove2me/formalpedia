-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_lower_eta
-- name    : Formalism.LFunctionChainParameters.LErr.error_lower_eta
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:53.167891+00:00
-- url     : https://prove2.me/theorems/2ee48aaa-6bf1-442b-ba42-9d5ec4270c2b
-- title:
--   LErr: error lower eta
-- statement:
--   The LErr construction uses the error lower eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L378-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L378-L403

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

theorem Formalism.LFunctionChainParameters.LErr.error_lower_eta : TraceTermLeErrorTerm := by sorry
