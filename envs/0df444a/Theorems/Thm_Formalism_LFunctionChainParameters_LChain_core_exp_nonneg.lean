-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_core_exp_nonneg
-- name    : Formalism.LFunctionChainParameters.LChain.core_exp_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:30:32.074531+00:00
-- url     : https://prove2.me/theorems/8cadc6dc-ecdf-4d6d-bf14-b500ee5934cb
-- title:
--   LChain: core exp nonneg
-- statement:
--   The LChain construction uses the core exp nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L692-L698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L692-L698

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

theorem Formalism.LFunctionChainParameters.LChain.core_exp_nonneg {eD eL K cHH eK CL ε x : ℝ} (h : ChainCore eD eL K cHH eK CL ε x) : 0 ≤ eD ∧ 0 ≤ eL ∧ 0 < ε := by sorry
