-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_collection_family_slope_gap
-- name    : Formalism.LFunctionChainParameters.LChain2.collection_family_slope_gap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:42:06.148628+00:00
-- url     : https://prove2.me/theorems/1e3404a3-8ae5-4d3d-93a8-5ec39a5370e0
-- title:
--   LChain2: collection family slope gap
-- statement:
--   The LChain2 construction uses the collection family slope gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L1874-L1899
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L1874-L1899

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
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
variable (v : InfinitePlace K) (m f T Mw : ℕ) (hb gG gE : ℝ)

theorem Formalism.LFunctionChainParameters.LChain2.collection_family_slope_gap (hT : 4 ≤ T) (hMpos : 0 < Mw) :
    wmean (collFam K v m f T Mw (hbT K f T) gG gE).du
      (fun u => muDef ((collFam K v m f T Mw (hbT K f T) gG gE).b u) ((collFam K v m f T Mw (hbT K f T) gG gE).X u)
        ((collFam K v m f T Mw (hbT K f T) gG gE).N' u) - (collFam K v m f T Mw (hbT K f T) gG gE).h u)
      - muMinDef (collFam K v m f T Mw (hbT K f T) gG gE).b' (collFam K v m f T Mw (hbT K f T) gG gE).X'
          (collFam K v m f T Mw (hbT K f T) gG gE).cc ≤ 0 := by sorry
