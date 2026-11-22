-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_text_key
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.text_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:47.398349+00:00
-- url     : https://prove2.me/theorems/fd33c18f-cace-406d-bec1-7417dc2c7876
-- title:
--   Sections Four To Six Transfer: text key
-- statement:
--   The Sections Four To Six Transfer construction uses the text key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L357-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L357-L383

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

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.text_key (ε E : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    8 ≤ x ∧ Real.log (bTx x ε) = x ^ ε ∧ 0 < bTx x ε ∧ 0 < aTx x ε ∧ 0 < bpTx x ε ∧
    ∀ K : ℝ, 0 < K → K ≤ x ^ E → K ≤ aTx x ε ∧ K * bpTx x ε ≤ aTx x ε ∧ x * K ≤ bpTx x ε := by sorry
