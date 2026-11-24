-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_superset_vec
-- name    : Formalism.MainNotions.PlaneGram.vala_superset_vec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:49.539376+00:00
-- url     : https://prove2.me/theorems/3c1317aa-79fc-40a7-9173-45d9544a4a33
-- title:
--   Plane Gram: vala superset vec
-- statement:
--   The Plane Gram construction uses the vala superset vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1040-L1043
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1040-L1043

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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}

theorem Formalism.MainNotions.PlaneGram.vala_superset_vec (hV2 : V2 K) {θ : ℝ} {S' : Finset L} (hsub : S ⊆ S')
    (hvec : ∀ i ∈ S', i ∉ S → sg i = true) {F : MvPolynomial (L × Fin r) K}
    (hF : vala sg S θ F) : vala sg S' θ F := by sorry
