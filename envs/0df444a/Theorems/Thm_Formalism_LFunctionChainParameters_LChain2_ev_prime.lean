-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ev_prime
-- name    : Formalism.LFunctionChainParameters.LChain2.ev_prime
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:46.060008+00:00
-- url     : https://prove2.me/theorems/30af56c7-33bc-407d-8287-f4f2998d9ea5
-- title:
--   LChain2: ev prime
-- statement:
--   The LChain2 construction uses the ev prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2267-L2306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L2267-L2306

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

theorem Formalism.LFunctionChainParameters.LChain2.ev_prime (f : ℕ) (x b : ℝ) (hf : 1 ≤ f) (hx : 1 ≤ x) (hE : 100 * (f : ℝ) ^ 2 * x ^ 2 ≤ b) :
    ∃ T : ℕ, T.Prime ∧ 4 * f ≤ T ∧ 18 * (f : ℝ) * x ^ 2 ≤ (T : ℝ) ∧
      4 * (f : ℝ) / (T : ℝ) * b ^ 2 + (f : ℝ) * Real.log ((T : ℝ) - 1) / ((T : ℝ) - 2) ≤ 1 ∧ (T : ℝ) ≤ b ^ 4 := by sorry
