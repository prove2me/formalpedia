-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_Model_hak
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model.hak
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:49.497499+00:00
-- url     : https://prove2.me/theorems/aace663f-4894-4418-b421-f5a409345da5
-- title:
--   Model: hak
-- statement:
--   The Model construction uses the hak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L678-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L678-L679

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model.hak : Real.exp 40 / Real.exp 2 = Real.exp 2 * Real.exp 36 := by sorry
