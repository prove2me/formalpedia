-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_add
-- name    : Formalism.MainNotions.PlaneGram.le_lord_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:22.3528+00:00
-- url     : https://prove2.me/theorems/5ab5921b-5c9f-48ea-8d47-616d19562d2f
-- title:
--   Plane Gram: le lord add
-- statement:
--   The Plane Gram construction uses the le lord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L24-L33

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

theorem Formalism.MainNotions.PlaneGram.le_lord_add {n : WithTop ℤ} {f g : LaurentPolynomial R} (hf : n ≤ lord f) (hg : n ≤ lord g) :
    n ≤ lord (f + g) := by sorry
