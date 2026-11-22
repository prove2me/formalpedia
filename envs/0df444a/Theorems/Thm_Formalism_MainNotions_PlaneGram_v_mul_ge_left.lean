-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_ge_left
-- name    : Formalism.MainNotions.PlaneGram.v_mul_ge_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:48.182895+00:00
-- url     : https://prove2.me/theorems/9ecff718-72c6-4c51-b787-a71ce322c188
-- title:
--   Plane Gram: v mul ge left
-- statement:
--   The Plane Gram construction uses the v mul ge left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L75-L77

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

theorem Formalism.MainNotions.PlaneGram.v_mul_ge_left {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : 0 ≤ v y) : c ≤ v (x * y) := by sorry
