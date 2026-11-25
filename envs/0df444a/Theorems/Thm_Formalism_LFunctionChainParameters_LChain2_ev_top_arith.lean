-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_top_arith
-- name    : Formalism.LFunctionChainParameters.LChain2.ev_top_arith
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:58:36.601648+00:00
-- url     : https://prove2.me/theorems/8db49e15-7a53-5cfc-833d-75a8af5f82a3
-- title:
--   LChain2: ev top arith
-- statement:
--   The LChain2 construction uses the ev top arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2321-L2330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2321-L2330

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)

theorem Formalism.LFunctionChainParameters.LChain2.ev_top_arith (c m A lA lT lg γ lx xe l2 E1 E2 : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlg : m * lg = lT - m * (l2 + xe)) (hlA : lA = lx + xe) (h : 2 + γ + l2 ≤ lx) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) :
    c * (m * A) ≤ c * (m * ((A * lA - A) - A * γ) - A * lT) + m * (c * A) * lg + E1 + E2 := by sorry
