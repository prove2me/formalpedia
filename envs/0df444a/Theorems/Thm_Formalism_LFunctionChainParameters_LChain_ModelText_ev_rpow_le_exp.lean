-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_ev_rpow_le_exp
-- name    : Formalism.LFunctionChainParameters.LChain.ModelText.ev_rpow_le_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:42.862688+00:00
-- url     : https://prove2.me/theorems/0e557928-7ee3-4cf5-8b5c-1c10aff1aa23
-- title:
--   Model Text: ev rpow le exp
-- statement:
--   The Model Text construction uses the ev rpow le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1234-L1247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1234-L1247

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

theorem Formalism.LFunctionChainParameters.LChain.ModelText.ev_rpow_le_exp (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in Filter.atTop, x ^ c ≤ Real.exp (x ^ δ) := by sorry
