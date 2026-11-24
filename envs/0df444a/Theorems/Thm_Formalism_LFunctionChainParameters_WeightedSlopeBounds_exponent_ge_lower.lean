-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_exponent_ge_lower
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.exponent_ge_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:40.615138+00:00
-- url     : https://prove2.me/theorems/d520ae5a-2238-4004-a34c-342c30918240
-- title:
--   Weighted Slope Bounds: exponent ge lower
-- statement:
--   The Weighted Slope Bounds construction uses the exponent ge lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L37-L40

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

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.exponent_ge_lower (hE : EComp5 D C) (u0 : U0) (u : W u0) :
    (m : ℝ) * (D.sumA * D.lg - C.cE * D.B0) ≤ D.Ee u0 u := by sorry
