-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_nonneg
-- name    : Formalism.MainNotions.PlaneGram.valS_C_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:23.071819+00:00
-- url     : https://prove2.me/theorems/ab46d6da-d7ee-4e37-bdd7-d0d57a61d655
-- title:
--   Plane Gram: val S C nonneg
-- statement:
--   The Plane Gram construction uses the val S C nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L148-L155

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

theorem Formalism.MainNotions.PlaneGram.valS_C_nonneg (a : K) : 0 ≤ valS sg S (C a : MvPolynomial (L × Fin r) K) := by sorry
