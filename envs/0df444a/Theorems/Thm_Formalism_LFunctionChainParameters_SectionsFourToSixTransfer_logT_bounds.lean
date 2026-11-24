-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_logT_bounds
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_bounds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:40.285378+00:00
-- url     : https://prove2.me/theorems/8098f7c0-c819-4321-bff9-92f886a6bc9d
-- title:
--   Sections Four To Six Transfer: log T bounds
-- statement:
--   The Sections Four To Six Transfer construction uses the log T bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L130-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L130-L146

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

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_bounds {X Gam y T : ℝ} (hX : 0 < X) (hG : 1 ≤ Gam) (hy : 0 < y)
    (h1 : X * Gam ^ (-(2 / y)) ≤ T) (h2 : T ≤ X * Gam ^ (-(2 / y)) * (1 + 1 / y)) :
    Real.log X - 2 * Real.log Gam / y ≤ Real.log T ∧
    Real.log T ≤ Real.log X - 2 * Real.log Gam / y + 1 / y := by sorry
