-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_rename
-- name    : Formalism.MainNotions.PlaneGram.substS_rename
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:48.06251+00:00
-- url     : https://prove2.me/theorems/43ff7477-72ae-4fb8-ac93-217cb2f61f7c
-- title:
--   Plane Gram: subst S rename
-- statement:
--   The Plane Gram construction uses the subst S rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L607-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L607-L624

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {L' : Type} [DecidableEq L'] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.substS_rename {R : Type} [CommRing R] (ι : K →+* R) (A B : Matrix (Fin r) (Fin r) R)
    (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    substS ι sg' S' A B (rename (Prod.map f id) F) =
      rename (Prod.map f id) (substS ι (sg' ∘ f) (S'.preimage f hf.injOn) A B F) := by sorry
