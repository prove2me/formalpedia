-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_coreNoAnalyticEv
-- name    : Formalism.LFunctionChainParameters.LChain.ModelEv.coreNoAnalyticEv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:39.478824+00:00
-- url     : https://prove2.me/theorems/cf08180b-786e-4def-8e34-55f2cacd99ff
-- title:
--   Model Ev: core No Analytic Ev
-- statement:
--   The Model Ev construction uses the core No Analytic Ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1219-L1223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1219-L1223

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model

theorem Formalism.LFunctionChainParameters.LChain.ModelEv.coreNoAnalyticEv : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ChainCoreNoAnalytic 1 1 1 1 2 ε x ∧ XLarge 1 1 2 0 0 ε x := by sorry
