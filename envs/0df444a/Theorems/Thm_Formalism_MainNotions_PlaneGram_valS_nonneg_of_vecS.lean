-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_vecS
-- name    : Formalism.MainNotions.PlaneGram.valS_nonneg_of_vecS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:58.000174+00:00
-- url     : https://prove2.me/theorems/2a7fa9e3-4705-40b9-be2b-f8b97a1fd85c
-- title:
--   Plane Gram: val S nonneg of vec S
-- statement:
--   The Plane Gram construction uses the val S nonneg of vec S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L568-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L568-L591

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

theorem Formalism.MainNotions.PlaneGram.valS_nonneg_of_vecS (F : MvPolynomial (L × Fin r) K)
    (h : ∀ α ∈ F.support, ∀ i a, α (i, a) ≠ 0 → i ∈ S → sg i = true) : 0 ≤ valS sg S F := by sorry
