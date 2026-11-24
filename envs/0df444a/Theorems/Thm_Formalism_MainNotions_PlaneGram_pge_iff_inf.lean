-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_iff_inf
-- name    : Formalism.MainNotions.PlaneGram.pge_iff_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:07:34.518958+00:00
-- url     : https://prove2.me/theorems/1d86fd7c-6abf-4140-8be8-63ab475f19b5
-- title:
--   Plane Gram: pge iff inf
-- statement:
--   The Plane Gram construction uses the pge iff inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L96-L104

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

theorem Formalism.MainNotions.PlaneGram.pge_iff_inf (n : WithTop ℤ) (G : MvPolynomial σ (LaurentPolynomial R)) :
    (n ≤ G.support.inf fun β => lord (G.coeff β)) ↔ pge n G := by sorry
