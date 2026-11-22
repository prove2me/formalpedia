-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_logT_of_window
-- name    : Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_of_window
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:38.819154+00:00
-- url     : https://prove2.me/theorems/6dbbcae2-d2df-4604-b14d-e1affd99b462
-- title:
--   Sections Four To Six Transfer: log T of window
-- statement:
--   The Sections Four To Six Transfer construction uses the log T of window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SecondPriceSumWeightsUncovered.lean#L158-L166

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

theorem Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_of_window {D : Data U0 W Top m f} {c5 Gam : ℝ} {X : ∀ u0, W u0 → ℝ}
    (hW : CountWindows D c5 Gam) (hLW : LevelWindow D Gam X) (u0 : U0) (u : W u0) :
    Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ Real.log (D.T u0 u) ∧
    Real.log (D.T u0 u) ≤ Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) + 1 / ((f : ℝ) * D.k) := by sorry
