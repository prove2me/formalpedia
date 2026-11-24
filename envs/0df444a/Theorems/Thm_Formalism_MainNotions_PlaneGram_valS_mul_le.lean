-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le
-- name    : Formalism.MainNotions.PlaneGram.valS_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:12.835679+00:00
-- url     : https://prove2.me/theorems/25389a80-da76-4b03-a0bc-10de23ff8814
-- title:
--   Plane Gram: val S mul le
-- statement:
--   The Plane Gram construction uses the val S mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L140-L143

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

theorem Formalism.MainNotions.PlaneGram.valS_mul_le (F G : MvPolynomial (L × Fin r) K) :
    valS sg S F + valS sg S G ≤ valS sg S (F * G) := by sorry
