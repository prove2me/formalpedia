-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_le_rpow_26
-- name    : Formalism.LFunctionChainParameters.LChain.le_rpow_26
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:46.509793+00:00
-- url     : https://prove2.me/theorems/5226fcb3-1675-4ae9-96bb-bf409c45bdcb
-- title:
--   LChain: le rpow 26
-- statement:
--   The LChain construction uses the le rpow 26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L130-L135

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
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr

theorem Formalism.LFunctionChainParameters.LChain.le_rpow_26 (ε x : ℝ) (hε : 0 < ε) (h1 : (26 : ℝ) ^ (8 / (3 * ε)) ≤ x) : 26 ≤ x ^ (3 * ε / 8) := by sorry
