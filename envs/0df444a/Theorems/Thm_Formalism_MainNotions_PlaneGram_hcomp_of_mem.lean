-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_of_mem
-- name    : Formalism.MainNotions.PlaneGram.hcomp_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:13.987865+00:00
-- url     : https://prove2.me/theorems/cc2e42be-2831-4f0f-b18f-504b7b2fc96a
-- title:
--   Plane Gram: hcomp of mem
-- statement:
--   The Plane Gram construction uses the hcomp of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L813-L820
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L813-L820

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
variable {L : Type} {r : ℕ}
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable [Fintype L]

theorem Formalism.MainNotions.PlaneGram.hcomp_of_mem (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (hF : F ∈ PolK K r d) :
    hcomp d F = F := by sorry
