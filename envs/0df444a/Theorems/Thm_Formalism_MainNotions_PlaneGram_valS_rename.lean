-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_rename
-- name    : Formalism.MainNotions.PlaneGram.valS_rename
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:20.968799+00:00
-- url     : https://prove2.me/theorems/ec276ede-ec53-4d56-a42c-fdec2d5bbdb1
-- title:
--   Plane Gram: val S rename
-- statement:
--   The Plane Gram construction uses the val S rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L626-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L626-L648

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

theorem Formalism.MainNotions.PlaneGram.valS_rename (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    valS sg' S' (rename (Prod.map f id) F) = valS (sg' ∘ f) (S'.preimage f hf.injOn) F := by sorry
