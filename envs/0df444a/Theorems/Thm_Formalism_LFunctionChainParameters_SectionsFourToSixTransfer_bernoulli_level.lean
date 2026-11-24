-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_bernoulli_level
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.bernoulli_level
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:42.196182+00:00
-- url     : https://prove2.me/theorems/823a5a44-e034-429e-9238-ce667f05d126
-- title:
--   Sections Four To Six Transfer: bernoulli level
-- statement:
--   The Sections Four To Six Transfer construction uses the bernoulli level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L310-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L310-L318

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

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.bernoulli_level (f : ℕ) {T : ℝ} (hT : 2 ≤ T) :
    1 - (f : ℝ) / (T - 1) ≤ (1 - 1 / (T - 1)) ^ f := by sorry
