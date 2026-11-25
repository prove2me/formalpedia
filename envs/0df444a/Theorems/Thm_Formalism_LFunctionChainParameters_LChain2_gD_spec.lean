-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_gD_spec
-- name    : Formalism.LFunctionChainParameters.LChain2.gD_spec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:14.942466+00:00
-- url     : https://prove2.me/theorems/957b809d-a8ec-5ec1-bf69-8bf79c847072
-- title:
--   LChain2: g D spec
-- statement:
--   The LChain2 construction uses the g D spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L408-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainLatticeSizesModelEventually.lean#L408-L417

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}

theorem Formalism.LFunctionChainParameters.LChain2.gD_spec (D : ArithData H) (hD : HostFacts D) (i : ℕ) :
    gD D i - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi (gD D i) := by sorry
