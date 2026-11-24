-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_mul
-- name    : Formalism.MainNotions.PlaneGram.pge_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:07:02.667793+00:00
-- url     : https://prove2.me/theorems/c45fafde-859a-445e-8e8b-bc37b7c09524
-- title:
--   Plane Gram: pge mul
-- statement:
--   The Plane Gram construction uses the pge mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L87-L91

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

theorem Formalism.MainNotions.PlaneGram.pge_mul {m n : WithTop ℤ} {F G : MvPolynomial σ (LaurentPolynomial R)} (hF : pge m F)
    (hG : pge n G) : pge (m + n) (F * G) := by sorry
