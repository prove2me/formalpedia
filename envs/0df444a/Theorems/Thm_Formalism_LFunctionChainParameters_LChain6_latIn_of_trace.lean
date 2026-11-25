-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_latIn_of_trace
-- name    : Formalism.LFunctionChainParameters.LChain6.latIn_of_trace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:59.940083+00:00
-- url     : https://prove2.me/theorems/23e97f6b-21da-4235-9d07-67877117c2a3
-- title:
--   LChain6: lat In of trace
-- statement:
--   The LChain6 construction uses the lat In of trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L403-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean#L403-L416

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
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hsg

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

theorem Formalism.LFunctionChainParameters.LChain6.latIn_of_trace {I : Type} [Fintype I] {m : ℕ} (F : FamC I m) (Rw : Rows F.toFam) (x ε sg Gam C0S de : ℝ)
    (hT : F.TraceIn Rw x ε sg Gam C0S) (hx : 0 < x) (hsg0 : 0 < sg) (hsg : sg ≤ 1 / 20) (hE8 : E8 x ε ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4) (hcor : ∑ u, ((F.d u : ℝ) - (F.r u : ℝ)) ≤ de * HilbertSchmidtNormSquare.Rs F.d)
    (w4 : ∀ u, F.Dstar / Gam ^ 2 / C0S ≤ (F.d u : ℝ)) :
    F.LatIn Rw sg Gam C0S (E7 x ε) := by sorry
