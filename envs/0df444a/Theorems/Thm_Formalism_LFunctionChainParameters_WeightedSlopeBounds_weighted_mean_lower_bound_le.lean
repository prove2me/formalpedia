-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_weighted_mean_lower_bound_le
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_lower_bound_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:11.424603+00:00
-- url     : https://prove2.me/theorems/23befe4b-9d1f-4e3c-b1c6-91b94e49c512
-- title:
--   Weighted Slope Bounds: weighted mean lower bound le
-- statement:
--   The Weighted Slope Bounds construction uses the weighted mean lower bound le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L162-L171

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_lower_bound_le (hS : D.HidaSetting C) (hCount : Count5 D C) (u0 : U0) :
    wmean (D.d u0) (Lo5 D C Xpp u0) ≤ C.cSl1 * D.IO u0 + K7v5 D C Xpp := by sorry
