-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes_eventually
-- name    : Formalism.LFunctionChainParameters.LErr.error_sizes_eventually
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:49.328747+00:00
-- url     : https://prove2.me/theorems/a1292bcb-b157-4f3b-b273-a6beabf8e0c8
-- title:
--   LErr: error sizes eventually
-- statement:
--   The LErr construction uses the error sizes eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L331-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L331-L338

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

theorem Formalism.LFunctionChainParameters.LErr.error_sizes_eventually : ErrorFormsEventual := by sorry
