-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_zTerms_real
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.zTerms_real
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:45.363968+00:00
-- url     : https://prove2.me/theorems/31705618-e280-4c77-beac-9317ed016d7d
-- title:
--   Sections Four To Six Transfer: z Terms real
-- statement:
--   The Sections Four To Six Transfer construction uses the z Terms real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L16-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L16-L82

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.zTerms_real {cZ cL cU a k mR b' Sc L La lk lkv LZ fR nT sA logT : ℝ}
    (hcZ : 0 ≤ cZ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (ha : 0 ≤ a) (hk : 1 ≤ k) (hmk : mR ≤ k)
    (hb' : 0 ≤ b') (hSc : 0 ≤ Sc) (hL : 0 ≤ L) (hLLa : L ≤ La) (hlk : lk ≤ La) (hlkv : lkv ≤ La)
    (hLZ : LZ ≤ cL * La) (hw1 : fR * k * (b' + Sc) ≤ nT * a) (hw2 : fR * k ^ 2 ≤ nT * a)
    (hn : 0 ≤ nT) (hf : 0 ≤ fR) (hm : 0 ≤ mR) (hs0 : 0 ≤ sA) (hs1 : sA ≤ nT * (2 * a / k))
    (hT : logT ≤ cU * mR * L) :
    sA * logT ≤ 2 * cU * (nT * a * La * (mR / k)) ∧
    cZ * nT * a * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * k * (b' + Sc) * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * Sc * logT ≤ cZ * cU * (nT * a * La * (mR / k)) ∧
    cZ * fR * k ^ 2 * LZ ≤ cZ * cL * (nT * a * La) ∧
    cZ * nT * a * lkv ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * (k * lkv) ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * logT ≤ cZ * cU * (nT * a * La) := by sorry
