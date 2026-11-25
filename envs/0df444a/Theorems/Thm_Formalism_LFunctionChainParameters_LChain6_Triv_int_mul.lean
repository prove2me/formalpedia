-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Triv_int_mul
-- name    : Formalism.LFunctionChainParameters.LChain6.Triv.int_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:29.991416+00:00
-- url     : https://prove2.me/theorems/f2aa1c49-2e9f-592c-b2db-a91c48f0547e
-- title:
--   Triv: int mul
-- statement:
--   The Triv construction uses the int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainAnalyticVariantOfTop.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainAnalyticVariantOfTop.lean#L96-L100

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainAnalyticVariantOfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain6.Triv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem Formalism.LFunctionChainParameters.LChain6.Triv.int_mul {a c : K} (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) :
    a * c ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
