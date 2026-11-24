-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_C_nonneg
-- name    : Formalism.MainNotions.PlaneGram.lord_C_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:07:25.283283+00:00
-- url     : https://prove2.me/theorems/b0e0943e-888e-424d-aeff-d7a5d1ebc865
-- title:
--   Plane Gram: lord C nonneg
-- statement:
--   The Plane Gram construction uses the lord C nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L58-L64

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

theorem Formalism.MainNotions.PlaneGram.lord_C_nonneg (a : R) : (0 : WithTop ℤ) ≤ lord (LaurentPolynomial.C a) := by sorry
