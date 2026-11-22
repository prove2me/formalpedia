-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff_pge
-- name    : Formalism.MainNotions.PlaneGram.le_valS_iff_pge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:23.65127+00:00
-- url     : https://prove2.me/theorems/54eba144-2bd9-45a9-9882-c93fa5775762
-- title:
--   Plane Gram: le val S iff pge
-- statement:
--   The Plane Gram construction uses the le val S iff pge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L120-L121

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)

theorem Formalism.MainNotions.PlaneGram.le_valS_iff_pge (n : WithTop ℤ) (F : MvPolynomial (L × Fin r) K) :
    n ≤ valS sg S F ↔ pge n (subV sg S F) := by sorry
