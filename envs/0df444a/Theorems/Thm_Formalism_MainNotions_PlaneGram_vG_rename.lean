-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vG_rename
-- name    : Formalism.MainNotions.PlaneGram.vG_rename
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:08:13.796864+00:00
-- url     : https://prove2.me/theorems/4bd3aacb-d68c-41da-9bbf-c83a969ad879
-- title:
--   Plane Gram: v G rename
-- statement:
--   The Plane Gram construction uses the v G rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L148-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsMonomialOrder.lean#L148-L163

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

theorem Formalism.MainNotions.PlaneGram.vG_rename (f : σ → τ) (hf : Function.Injective f) (F : MvPolynomial σ K) :
    vG v (rename f F) = vG v F := by sorry
