-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes_weak_false
-- name    : Formalism.LFunctionChainParameters.LErr.error_sizes_weak_false
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:30.651066+00:00
-- url     : https://prove2.me/theorems/07899c8e-9abe-482e-80bd-1295757b3943
-- title:
--   LErr: error sizes weak false
-- statement:
--   The LErr construction uses the error sizes weak false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L471-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L471-L488

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

theorem Formalism.LFunctionChainParameters.LErr.error_sizes_weak_false : ¬ ErrorFormsWeakWindowsFalse := by sorry
