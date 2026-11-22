-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_threshold_constant_nonneg
-- name    : Formalism.LFunctionChainParameters.LBrDiv.threshold_constant_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:51:26.683056+00:00
-- url     : https://prove2.me/theorems/9c227820-4d76-4233-8b68-4667722f6365
-- title:
--   LBr Div: threshold constant nonneg
-- statement:
--   The LBr Div construction uses the threshold constant nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean#L503-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean#L503-L506

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

theorem Formalism.LFunctionChainParameters.LBrDiv.threshold_constant_nonneg {H : Type} [Fintype H] (m : ℕ) (x ε : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (x ^ ε) * x ^ ε := by sorry
