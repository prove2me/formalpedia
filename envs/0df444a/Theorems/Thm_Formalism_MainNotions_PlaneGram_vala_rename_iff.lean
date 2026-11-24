-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_rename_iff
-- name    : Formalism.MainNotions.PlaneGram.vala_rename_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:42.791808+00:00
-- url     : https://prove2.me/theorems/7fc9bc0c-d584-4fff-926a-c1ed943a9833
-- title:
--   Plane Gram: vala rename iff
-- statement:
--   The Plane Gram construction uses the vala rename iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1020-L1023
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1020-L1023

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
variable {sg S}

theorem Formalism.MainNotions.PlaneGram.vala_rename_iff {L' : Type} [DecidableEq L'] (f : L → L') (hf : Function.Injective f)
    (sg' : L' → Bool) (S' : Finset L') (θ : ℝ) (F : MvPolynomial (L × Fin r) K) :
    vala sg' S' θ (rename (Prod.map f id) F) ↔ vala (sg' ∘ f) (S'.preimage f hf.injOn) θ F := by sorry
