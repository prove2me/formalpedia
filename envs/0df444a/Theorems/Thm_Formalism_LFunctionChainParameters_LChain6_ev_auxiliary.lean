-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_ev_auxiliary
-- name    : Formalism.LFunctionChainParameters.LChain6.ev_auxiliary
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:02.194406+00:00
-- url     : https://prove2.me/theorems/f76be692-a5e9-492b-91b3-60201eb0e170
-- title:
--   LChain6: ev auxiliary
-- statement:
--   The LChain6 construction uses the ev auxiliary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L289-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L289-L359

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

theorem Formalism.LFunctionChainParameters.LChain6.ev_auxiliary (ε A c' K cHH : ℝ) (hε : 0 < ε) (hε4 : ε < 1 / 4) (hc' : 0 < c') :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 20 ≤ x ∧ E8 x ε ≤ x ^ (-cHH) / 2 ∧ 6 ≤ x ^ ((1 : ℝ) / 2 - ε) ∧
      2 * K + 2 ≤ 15 * x ^ ((1 : ℝ) / 2 - ε) ∧ 4 * Real.exp (x ^ (ε / 4)) ≤ bpTx x ε ∧
      ∀ f : ℝ, 0 ≤ f → f ≤ 2 * x ^ A →
        2 * f * (x + 1) * Real.exp (-c' * x ^ (ε / 8)) ≤ 1 / x ∧
        6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) ≤ bTx x ε / x := by sorry
