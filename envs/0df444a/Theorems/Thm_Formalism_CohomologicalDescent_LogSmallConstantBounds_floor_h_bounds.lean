-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_floor_h_bounds
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.floor_h_bounds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:25.245299+00:00
-- url     : https://prove2.me/theorems/0b6003cf-e972-4fd7-afb3-d2d5f6a67cde
-- title:
--   Log Small Constant Bounds: floor h bounds
-- statement:
--   The Log Small Constant Bounds construction uses the floor h bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L861-L873
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L861-L873

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.floor_h_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    (1 : ℝ) ≤ (⌊P.h⌋₊ : ℝ) ∧ (⌊P.h⌋₊ : ℝ) ≤ P.h ∧ (⌊P.h⌋₊ : ℝ) < P.lJ ^ 2 ∧
      0 ≤ Real.log (⌊P.h⌋₊ : ℝ) ∧ Real.log (⌊P.h⌋₊ : ℝ) ≤ Real.log P.h := by sorry
