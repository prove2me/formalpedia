-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_model_windows0
-- name    : Formalism.LFunctionChainParameters.LErr.model_windows0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:59.977662+00:00
-- url     : https://prove2.me/theorems/6ecbe340-586e-48ee-b6a8-8e2f671a0218
-- title:
--   LErr: model windows0
-- statement:
--   The LErr construction uses the model windows0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L448-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L448-L460

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

theorem Formalism.LFunctionChainParameters.LErr.model_windows0 (η cHH : ℝ) (hη : 0 ≤ η) (hc : 0 ≤ cHH) :
    ErrWindows0 (modelD η) (modelC cHH) 3 1 1 := by sorry
