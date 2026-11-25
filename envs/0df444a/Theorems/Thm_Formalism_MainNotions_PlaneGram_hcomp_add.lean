-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_add
-- name    : Formalism.MainNotions.PlaneGram.hcomp_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:06.096808+00:00
-- url     : https://prove2.me/theorems/58acaa4d-106a-5b07-b1c1-1f4041986268
-- title:
--   Plane Gram: hcomp add
-- statement:
--   The Plane Gram construction uses the hcomp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L794-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L794-L796

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

theorem Formalism.MainNotions.PlaneGram.hcomp_add (d : L → ℕ) (F G : MvPolynomial (L × Fin r) K) :
    hcomp d (F + G) = hcomp d F + hcomp d G := by sorry
