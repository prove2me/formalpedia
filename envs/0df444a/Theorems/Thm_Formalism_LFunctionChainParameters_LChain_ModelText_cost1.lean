-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_cost1
-- name    : Formalism.LFunctionChainParameters.LChain.ModelText.cost1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:19.581156+00:00
-- url     : https://prove2.me/theorems/71cbf8ba-9fe1-4e85-82d0-7fb7a2dfc5b7
-- title:
--   Model Text: cost1
-- statement:
--   The Model Text construction uses the cost1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1481-L1502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1481-L1502

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
open Formalism.LFunctionChainParameters.LChain.ModelText

theorem Formalism.LFunctionChainParameters.LChain.ModelText.cost1 {x ε n : ℝ} (h48 : 48 ≤ x) (_hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f1 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 8))) : 2 * (2 * n) * (x + 1) * thTx x ε ≤ 1 / x := by sorry
