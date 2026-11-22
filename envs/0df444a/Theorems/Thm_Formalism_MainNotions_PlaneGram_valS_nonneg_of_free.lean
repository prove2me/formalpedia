-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_free
-- name    : Formalism.MainNotions.PlaneGram.valS_nonneg_of_free
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:11.750974+00:00
-- url     : https://prove2.me/theorems/fcd8f46a-5282-4fe3-ac7a-1d0fc9a93fd9
-- title:
--   Plane Gram: val S nonneg of free
-- statement:
--   The Plane Gram construction uses the val S nonneg of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L593-L595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L593-L595

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
variable {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)

theorem Formalism.MainNotions.PlaneGram.valS_nonneg_of_free (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i ∈ S, ∀ a, α (i, a) = 0) : 0 ≤ valS sg S F := by sorry
