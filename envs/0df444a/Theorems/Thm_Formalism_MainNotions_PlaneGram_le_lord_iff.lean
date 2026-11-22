-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_lord_iff
-- name    : Formalism.MainNotions.PlaneGram.le_lord_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:59.691688+00:00
-- url     : https://prove2.me/theorems/90e540d8-a979-488c-a7ed-8c25c93f5b20
-- title:
--   Plane Gram: le lord iff
-- statement:
--   The Plane Gram construction uses the le lord iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L13-L17

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

theorem Formalism.MainNotions.PlaneGram.le_lord_iff (n : WithTop ℤ) (f : LaurentPolynomial R) :
    n ≤ lord f ↔ ∀ k : ℤ, f.coeff k ≠ 0 → n ≤ (k : WithTop ℤ) := by sorry
