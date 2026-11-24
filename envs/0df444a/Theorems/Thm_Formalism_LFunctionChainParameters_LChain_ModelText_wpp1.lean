-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_wpp1
-- name    : Formalism.LFunctionChainParameters.LChain.ModelText.wpp1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:04.156586+00:00
-- url     : https://prove2.me/theorems/bbe9c03f-04ab-4b03-ab00-aa70f8929c33
-- title:
--   Model Text: wpp1
-- statement:
--   The Model Text construction uses the wpp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1539-L1558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1539-L1558

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

theorem Formalism.LFunctionChainParameters.LChain.ModelText.wpp1 {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f3 : x ^ (15 : ℝ) ≤ Real.exp (x ^ (ε / 3))) (f6 : 2 ≤ x ^ (2 * ε / 3)) : 1 ≤ wppTx x ε n := by sorry
