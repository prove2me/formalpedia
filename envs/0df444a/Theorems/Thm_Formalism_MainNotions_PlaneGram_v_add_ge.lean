-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_add_ge
-- name    : Formalism.MainNotions.PlaneGram.v_add_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:16.511051+00:00
-- url     : https://prove2.me/theorems/1b1f6503-5a93-4647-a6cb-98c0f04056d8
-- title:
--   Plane Gram: v add ge
-- statement:
--   The Plane Gram construction uses the v add ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L83-L84

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
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
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}

theorem Formalism.MainNotions.PlaneGram.v_add_ge {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : c ≤ v y) : c ≤ v (x + y) := by sorry
