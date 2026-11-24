-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hMat_mem
-- name    : Formalism.MainNotions.PlaneGram.hMat_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:25.793938+00:00
-- url     : https://prove2.me/theorems/9a131b71-1251-4fa7-94d6-601c71e07792
-- title:
--   Plane Gram: h Mat mem
-- statement:
--   The Plane Gram construction uses the h Mat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L551-L564
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L551-L564

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

theorem Formalism.MainNotions.PlaneGram.hMat_mem (r : ℕ) (a b : Fin r) :
    hMat K r a b ∈ (Polynomial.toLaurent : Polynomial (GenF K r) →+* LauF K r).range := by sorry
