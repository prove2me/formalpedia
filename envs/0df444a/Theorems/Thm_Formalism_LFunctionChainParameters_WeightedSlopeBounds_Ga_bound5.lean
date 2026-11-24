-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_Ga_bound5
-- name    : Formalism.LFunctionChainParameters.WeightedSlopeBounds.Ga_bound5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:02.977371+00:00
-- url     : https://prove2.me/theorems/2c9e97c8-0395-4ee3-9bc5-47b690eb9368
-- title:
--   Weighted Slope Bounds: Ga bound5
-- statement:
--   The Weighted Slope Bounds construction uses the Ga bound5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L113-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean#L113-L160

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

theorem Formalism.LFunctionChainParameters.WeightedSlopeBounds.Ga_bound5 (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C) (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hSI : D.SlopeIneq) (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + K0v5 D C
      + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by sorry
