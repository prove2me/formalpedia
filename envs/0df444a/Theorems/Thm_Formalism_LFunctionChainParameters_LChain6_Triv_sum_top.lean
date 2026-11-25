-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Triv_sum_top
-- name    : Formalism.LFunctionChainParameters.LChain6.Triv.sum_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:02.443507+00:00
-- url     : https://prove2.me/theorems/ce268871-17b3-5580-aaa8-43b3e8b81b51
-- title:
--   Triv: sum top
-- statement:
--   The Triv construction uses the sum top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainAnalyticVariantOfTop.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChainAnalyticVariantOfTop.lean#L174-L175

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
variable (v0 : InfinitePlace K)
  {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
  (D : ArithData H) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (P : PrimeWindowSizeBounds.Par) (T : H → ℕ)
  (Mw : ℕ) (gE : ℝ)

theorem Formalism.LFunctionChainParameters.LChain6.Triv.sum_top (φ : H → ℝ) : ∑ t ∈ TT.map (topPhi H), φ t.1.2 = ∑ t ∈ TT, φ t := by sorry
