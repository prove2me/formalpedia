-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_nonneg_of_mem
-- name    : Formalism.MainNotions.PlaneGram.lord_nonneg_of_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:07:23.978182+00:00
-- url     : https://prove2.me/theorems/0eed742e-2bc7-46e7-8d79-7f18b7338fd0
-- title:
--   Plane Gram: lord nonneg of mem
-- statement:
--   The Plane Gram construction uses the lord nonneg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L540-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L540-L549

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
variable {K : Type} [Field K]

theorem Formalism.MainNotions.PlaneGram.lord_nonneg_of_mem {R : Type} [CommRing R] (f : LaurentPolynomial R)
    (hf : f ∈ (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).range) : 0 ≤ lord f := by sorry
