-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_deF_bound
-- name    : Formalism.LFunctionChainParameters.LChain6.deF_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:47.400957+00:00
-- url     : https://prove2.me/theorems/853f056a-0116-5034-bc14-5a226b08b01c
-- title:
--   LChain6: de F bound
-- statement:
--   The LChain6 construction uses the de F bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L361-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L361-L397

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AnalyticFirstToLatticeDiscriminant
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

theorem Formalism.LFunctionChainParameters.LChain6.deF_bound {I : Type} [Fintype I] {m : ℕ} (F : Fam I m) (f : ℕ) (T0 : ℝ) (hT0 : 0 < T0)
    (h : ∀ u, F.du u = F.dM u * (1 - 1 / ((F.T u : ℝ) - 1)) ^ f ∧ 2 ≤ (F.T u : ℝ) ∧ T0 ≤ (F.T u : ℝ))
    (hpos : 0 < MatrixLatticeEstimates.RsG F.ιf) :
    0 ≤ F.deF ∧ F.deF ≤ 2 * (f : ℝ) / T0 ∧
      ∑ u, ((Fintype.card (F.ιf u) : ℝ) - (Fintype.card (F.ι u) : ℝ)) ≤ F.deF * MatrixLatticeEstimates.RsG F.ιf := by sorry
