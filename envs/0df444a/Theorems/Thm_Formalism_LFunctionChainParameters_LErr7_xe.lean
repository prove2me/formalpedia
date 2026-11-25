-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr7_xe
-- name    : Formalism.LFunctionChainParameters.LErr7.xe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:50.138013+00:00
-- url     : https://prove2.me/theorems/b8e99fb7-5bc5-54ae-a6ab-5d806c7c065b
-- title:
--   LErr7: xe
-- statement:
--   The LErr7 construction uses the xe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ErrorExponentBelowOnesFalse.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ErrorExponentBelowOnesFalse.lean#L23-L25

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsEventualPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ErrorExponentBelowOnesFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr7
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr
set_option linter.unusedVariables false

theorem Formalism.LFunctionChainParameters.LErr7.xe : ((10 : ℝ) ^ 400) ^ ((1 : ℝ) / 100) = 10 ^ 4 := by sorry
