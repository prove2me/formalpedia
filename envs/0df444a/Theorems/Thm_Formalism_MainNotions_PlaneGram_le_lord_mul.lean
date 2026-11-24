-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_mul
-- name    : Formalism.MainNotions.PlaneGram.le_lord_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:07:18.543337+00:00
-- url     : https://prove2.me/theorems/39e482fb-dd78-4154-8925-0c07b4d365f3
-- title:
--   Plane Gram: le lord mul
-- statement:
--   The Plane Gram construction uses the le lord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L45-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L45-L56

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
variable {R : Type} [Semiring R]

theorem Formalism.MainNotions.PlaneGram.le_lord_mul {m n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : m ≤ lord f) (hg : n ≤ lord g) :
    m + n ≤ lord (f * g) := by sorry
