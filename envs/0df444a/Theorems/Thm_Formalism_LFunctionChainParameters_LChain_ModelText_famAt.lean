-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_famAt
-- name    : Formalism.LFunctionChainParameters.LChain.ModelText.famAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:59.262188+00:00
-- url     : https://prove2.me/theorems/01f3fe12-f73b-4f8e-a88d-cad917d45f2b
-- title:
--   Model Text: fam At
-- statement:
--   The Model Text construction uses the fam At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1321-L1473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean#L1321-L1473

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.LChain.ModelText.famAt (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hx : 3 ≤ x)
    (hT : 1 ≤ x ∧ 1 ≤ bTx x ε ∧ Real.log (bTx x ε) = x ^ ε ∧ Real.log (aTx x ε) + x ^ (ε / 3) ≤ 2 * x ^ ε ∧
      kTx x ε ≤ aTx x ε ∧ 0 ≤ bpTx x ε ∧ kTx x ε * bpTx x ε ≤ aTx x ε ∧
      0 ≤ XppTx x ε (Fintype.card H) ∧ XppTx x ε (Fintype.card H) ≤ aTx x ε)
    (hnlo : x ^ (2 + 8 * ε) ≤ (Fintype.card H : ℝ))
    (hmlo : x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m) (hmhi : (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16))
    (h2 : 2 ≤ x ^ (9 * ε / 16))
    (hTT : x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 ≤ TT.card)
    (hT2 : x ^ (-ε) * (Fintype.card H : ℝ) ≤ T2.card)
    (hc1 : 2 * (2 * (Fintype.card H : ℝ)) * (x + 1) * thTx x ε ≤ 1 / x)
    (hc2 : 6 * (2 * (Fintype.card H : ℝ)) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x)
    (hw1 : 1 ≤ wppTx x ε (Fintype.card H)) : AllSizes x ε m TT T2 := by sorry
