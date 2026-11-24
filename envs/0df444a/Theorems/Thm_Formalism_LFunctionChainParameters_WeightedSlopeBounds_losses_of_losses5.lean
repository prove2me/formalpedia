-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_losses_of_losses5
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.losses_of_losses5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:40.315258+00:00
-- url     : https://prove2.me/theorems/246ca587-911f-493c-ab8e-3a1d40b5287c
-- title:
--   Weighted Slope Bounds: losses of losses5
-- statement:
--   The Weighted Slope Bounds construction uses the losses of losses5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L42-L48

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

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.losses_of_losses5 [Nonempty U0] (h : LossBounds D C) : D.Losses C := by sorry
