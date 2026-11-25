-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_joint_sat
-- name    : Formalism.LFunctionChainParameters.LBrDiv.joint_sat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:28.30809+00:00
-- url     : https://prove2.me/theorems/a7309c02-7bdd-4c38-9319-dae591669967
-- title:
--   LBr Div: joint sat
-- statement:
--   The LBr Div construction uses the joint sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean#L623-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PBrDiv.lean#L623-L644

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

theorem Formalism.LFunctionChainParameters.LBrDiv.joint_sat :
    ParHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε)) (Fintype.card (Fin 1) : ℝ) ∧
    StepHyp satD satP 1 (satD.x ^ (satC.eDiv * satD.ε))
      (Finset.univ.map (Function.Embedding.refl (Fin 1))) (fun _ => 0) () () satSt ∧
    Per satD 1 ∧ 0 < satD.v ∧ satC.cDiv = 50 * satP.C0 + 10 ∧ satD.Fo () = 2 * satSt.FoP := by sorry
