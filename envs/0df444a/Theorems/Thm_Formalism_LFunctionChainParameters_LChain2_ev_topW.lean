-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_topW
-- name    : Formalism.LFunctionChainParameters.LChain2.ev_topW
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:51:14.142002+00:00
-- url     : https://prove2.me/theorems/33c8afdf-5b37-447d-8c1d-220d993d9135
-- title:
--   LChain2: ev top W
-- statement:
--   The LChain2 construction uses the ev top W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2464-L2497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2464-L2497

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.LChain2.ev_topW (x ε lg : ℝ) (m T N : ℕ) (TT T2 : Finset H) (h48 : 48 ≤ x) (hlx : 4 ≤ Real.log x)
    (hLa : 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)) (hk0 : 0 < ModelText.kTx x ε)
    (hmlg : (m : ℝ) * lg = Real.log (T : ℝ) - (m : ℝ) * (Real.log 2 + x ^ ε)) :
    TopAtLevel Model.DA (fun _ => 0) (evG x ε lg) evC N TT T2
      (fun _ => aTx x ε) (ModelText.wF x ε m TT T2) (fun _ => T) := by sorry
