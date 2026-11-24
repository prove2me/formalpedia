-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_zero
-- name    : Formalism.MainNotions.PlaneGram.pge_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:07:21.42158+00:00
-- url     : https://prove2.me/theorems/fee040b3-12f4-42fb-854e-83301a0c8234
-- title:
--   Plane Gram: pge zero
-- statement:
--   The Plane Gram construction uses the pge zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L75-L76

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

theorem Formalism.MainNotions.PlaneGram.pge_zero (n : WithTop ℤ) : pge n (0 : MvPolynomial σ (LaurentPolynomial R)) := by sorry
