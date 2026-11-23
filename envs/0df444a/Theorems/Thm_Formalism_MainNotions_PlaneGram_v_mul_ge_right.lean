-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_ge_right
-- name    : Formalism.MainNotions.PlaneGram.v_mul_ge_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:01.39643+00:00
-- url     : https://prove2.me/theorems/dbe5bb5b-6aff-47ba-8b9e-0b4ea397cc04
-- title:
--   Plane Gram: v mul ge right
-- statement:
--   The Plane Gram construction uses the v mul ge right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L79-L81

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

theorem Formalism.MainNotions.PlaneGram.v_mul_ge_right {x y : K} {c : WithTop ℚ} (hx : 0 ≤ v x) (hy : c ≤ v y) : c ≤ v (x * y) := by sorry
