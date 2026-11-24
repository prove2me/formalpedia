-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_z_to_slopes
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.z_to_slopes
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:54.208242+00:00
-- url     : https://prove2.me/theorems/d5d2ef7e-93f9-42ff-97cf-b4dc081d3090
-- title:
--   Sections Four To Six Transfer: z to slopes
-- statement:
--   The Sections Four To Six Transfer construction uses the z to slopes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L98-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L98-L128

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

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.z_to_slopes : ZToSlopes := by sorry
