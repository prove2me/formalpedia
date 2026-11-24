-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_ddiv_letter
-- name    : Formalism.MainNotions.PlaneGram.vala_ddiv_letter
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:07:54.053943+00:00
-- url     : https://prove2.me/theorems/8847b907-a338-44e4-96b7-8163d50f7e76
-- title:
--   Plane Gram: vala ddiv letter
-- statement:
--   The Plane Gram construction uses the vala ddiv letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1065-L1072
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1065-L1072

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

theorem Formalism.MainNotions.PlaneGram.vala_ddiv_letter (hV2 : V2 K) {θ : ℝ} (i : L) (β : Fin r →₀ ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - absE β) (ddiv (onLetter i β) F) := by sorry
