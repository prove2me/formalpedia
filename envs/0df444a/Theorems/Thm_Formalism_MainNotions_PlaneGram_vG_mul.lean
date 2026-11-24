-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_mul
-- name    : Formalism.MainNotions.PlaneGram.vG_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:08:03.3893+00:00
-- url     : https://prove2.me/theorems/0e52d36a-d170-47ef-9eda-582bee4e9fb8
-- title:
--   Plane Gram: v G mul
-- statement:
--   The Plane Gram construction uses the v G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L77-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L77-L139

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v}
variable {σ τ : Type}

theorem Formalism.MainNotions.PlaneGram.vG_mul (F G : MvPolynomial σ K) : vG v (F * G) = vG v F + vG v G := by sorry
