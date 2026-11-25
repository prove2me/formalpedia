-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_constsExist
-- name    : Formalism.LFunctionChainParameters.LChain2.constsExist
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:39.184116+00:00
-- url     : https://prove2.me/theorems/b49968b7-b1a5-5202-8e66-a1b0669a26f5
-- title:
--   LChain2: consts Exist
-- statement:
--   The LChain2 construction uses the consts Exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L1125-L1244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L1125-L1244

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

theorem Formalism.LFunctionChainParameters.LChain2.constsExist {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} [Fintype Top]
    {m f : ℕ} (Dd : Data U0 W Top m f) (eDiv eLoss cHH c0 : ℝ)
    (hx : 0 < Dd.x) (hnT : 0 < Dd.nT) (ha : 0 < Dd.a) (hLa : 0 < Dd.La) (hm : 1 ≤ m) (hB0 : 0 < Dd.B0)
    (hNc : 0 ≤ Dd.Nc) (hb : 0 < Dd.b) (hL : 0 < Dd.L) (hk : 1 ≤ Dd.k) (hT : ∀ u0 u, 1 ≤ Dd.T u0 u)
    (hhw : ∀ u0 u u', Dd.h u0 u = Dd.h u0 u') (hTw : ∀ u0 u u', Dd.T u0 u = Dd.T u0 u') :
    ∃ cDiv cE cCount cSlope cLoss : ℝ, 0 ≤ cDiv ∧ 0 ≤ cE ∧ 0 ≤ cCount ∧ 0 ≤ cSlope ∧ 0 ≤ cLoss ∧
      Dd.DIV ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      EComp5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.HComp ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Count5 Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      Dd.Slopes ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ ∧
      LossBounds Dd ⟨cDiv, eDiv, cE, 0, cCount, cSlope, c0, cLoss, eLoss, cHH⟩ := by sorry
