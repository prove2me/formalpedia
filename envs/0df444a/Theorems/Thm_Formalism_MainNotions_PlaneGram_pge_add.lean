-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_add
-- name    : Formalism.MainNotions.PlaneGram.pge_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:07:01.832253+00:00
-- url     : https://prove2.me/theorems/a38021e5-3605-40e2-806a-9c7464ceaca1
-- title:
--   Plane Gram: pge add
-- statement:
--   The Plane Gram construction uses the pge add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L78-L80

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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
variable {R : Type} [CommSemiring R] {σ : Type}

theorem Formalism.MainNotions.PlaneGram.pge_add {n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge n F)
    (hG : pge n G) : pge n (F + G) := by sorry
