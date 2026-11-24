-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_sizesOf
-- name    : Formalism.LFunctionChainParameters.LChain.ModelEv.sizesOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:37.527925+00:00
-- url     : https://prove2.me/theorems/bdefe238-e191-418f-bbc5-5f8f64ace33f
-- title:
--   Model Ev: sizes Of
-- statement:
--   The Model Ev construction uses the sizes Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L942-L1132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L942-L1132

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
set_option maxHeartbeats 1600000

theorem Formalism.LFunctionChainParameters.LChain.ModelEv.sizesOf (x ε b : ℝ) (m N n : ℕ) (hcard : Fintype.card H = n)
    (hx : 3 ≤ x) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : x ≤ n) (hb : b = 12 * n * (x + 1) * x)
    (hm1 : x ^ ((1 : ℝ) / 2 - ε) ≤ m) (hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) (hmx : (m : ℝ) ≤ x)
    (hk : x * m ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) (hL : Real.log b ≤ 2 * x ^ ε) (hN : x * b ≤ N)
    (hl3 : 3 ≤ Real.log x) :
    SizesAt 1 1 2 ε x := by sorry
