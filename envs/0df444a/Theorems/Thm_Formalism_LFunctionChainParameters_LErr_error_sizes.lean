-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes
-- name    : Formalism.LFunctionChainParameters.LErr.error_sizes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:36.833738+00:00
-- url     : https://prove2.me/theorems/9bb646eb-f7f6-44d7-bf77-7d96da6ad0cf
-- title:
--   LErr: error sizes
-- statement:
--   The LErr construction uses the error sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L259-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L259-L317

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
set_option maxHeartbeats 1000000

theorem Formalism.LFunctionChainParameters.LErr.error_sizes : ErrorFormsUnderWindows := by sorry
