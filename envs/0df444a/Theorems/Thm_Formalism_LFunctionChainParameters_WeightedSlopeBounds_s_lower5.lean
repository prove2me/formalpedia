-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_s_lower5
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.s_lower5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:25.597805+00:00
-- url     : https://prove2.me/theorems/e0a5329b-2b48-4a73-a94a-304870ff2759
-- title:
--   Weighted Slope Bounds: s lower5
-- statement:
--   The Weighted Slope Bounds construction uses the s lower5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L50-L66

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

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.s_lower5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 - wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0 := by sorry
