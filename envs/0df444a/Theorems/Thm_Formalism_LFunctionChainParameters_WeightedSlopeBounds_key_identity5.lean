-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_key_identity5
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.key_identity5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:38.24899+00:00
-- url     : https://prove2.me/theorems/668ae34f-8e58-4320-85e7-4f4c80f64665
-- title:
--   Weighted Slope Bounds: key identity5
-- statement:
--   The Weighted Slope Bounds construction uses the key identity5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L105-L111

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

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.key_identity5 (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * Lam5 D C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k)) := by sorry
