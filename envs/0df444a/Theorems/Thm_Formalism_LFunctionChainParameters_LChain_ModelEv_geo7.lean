-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_geo7
-- name    : Formalism.LFunctionChainParameters.LChain.ModelEv.geo7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:16.24629+00:00
-- url     : https://prove2.me/theorems/75621708-e058-4984-b848-e5b1d5bbfcf1
-- title:
--   Model Ev: geo7
-- statement:
--   The Model Ev construction uses the geo7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L894-L901
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L894-L901

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.LChain.ModelEv.geo7 (a : ℝ) (N : ℕ) : ∑ i ∈ Icc 1 N, a / (7 : ℝ) ^ i + a / (6 * 7 ^ N) = a / 6 := by sorry
