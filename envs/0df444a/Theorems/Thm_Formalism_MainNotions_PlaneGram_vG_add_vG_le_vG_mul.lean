-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_add_vG_le_vG_mul
-- name    : Formalism.MainNotions.PlaneGram.vG_add_vG_le_vG_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:55.468276+00:00
-- url     : https://prove2.me/theorems/8d25f3e2-4126-4339-9b87-5609371e47fe
-- title:
--   Plane Gram: v G add v G le v G mul
-- statement:
--   The Plane Gram construction uses the v G add v G le v G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L61-L69

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

theorem Formalism.MainNotions.PlaneGram.vG_add_vG_le_vG_mul (F G : MvPolynomial σ K) : vG v F + vG v G ≤ vG v (F * G) := by sorry
