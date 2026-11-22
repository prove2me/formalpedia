-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_fk_pos
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.fk_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:02.406157+00:00
-- url     : https://prove2.me/theorems/911439ff-f3df-449d-9920-96e018444aaf
-- title:
--   Sections Four To Six Transfer: fk pos
-- statement:
--   The Sections Four To Six Transfer construction uses the fk pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L151-L156

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
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.fk_pos {D : Data U0 W Top m f} {c5 Gam : ℝ} (hW : CountWindows D c5 Gam) :
    0 < (f : ℝ) * D.k ∧ 1 / ((f : ℝ) * D.k) ≤ 1 := by sorry
