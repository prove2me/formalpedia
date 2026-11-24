-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_mul_le
-- name    : Formalism.MainNotions.PlaneGram.valS_C_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:01.112232+00:00
-- url     : https://prove2.me/theorems/3efc10a8-ce76-4d39-9888-7286ca0a1087
-- title:
--   Plane Gram: val S C mul le
-- statement:
--   The Plane Gram construction uses the val S C mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L157-L162

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

theorem Formalism.MainNotions.PlaneGram.valS_C_mul_le (a : K) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (C a * F) := by sorry
