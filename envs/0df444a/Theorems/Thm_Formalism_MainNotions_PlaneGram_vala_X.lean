-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_X
-- name    : Formalism.MainNotions.PlaneGram.vala_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:08:03.29481+00:00
-- url     : https://prove2.me/theorems/8b291602-7b48-4911-848a-a1389a59423e
-- title:
--   Plane Gram: vala X
-- statement:
--   The Plane Gram construction uses the vala X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1045-L1055
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1045-L1055

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

theorem Formalism.MainNotions.PlaneGram.vala_X (hV2 : V2 K) (i : L) (a : Fin r) :
    vala sg S (if sg i then 0 else -1) (X (i, a) : MvPolynomial (L × Fin r) K) := by sorry
