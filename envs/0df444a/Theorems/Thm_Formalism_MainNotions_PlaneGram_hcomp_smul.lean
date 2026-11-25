-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_smul
-- name    : Formalism.MainNotions.PlaneGram.hcomp_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:36.276797+00:00
-- url     : https://prove2.me/theorems/a49870b0-e2b1-452f-a516-db1fd0efbfd6
-- title:
--   Plane Gram: hcomp smul
-- statement:
--   The Plane Gram construction uses the hcomp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L798-L800
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L798-L800

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

theorem Formalism.MainNotions.PlaneGram.hcomp_smul (d : L → ℕ) (a : K) (F : MvPolynomial (L × Fin r) K) :
    hcomp d (a • F) = a • hcomp d F := by sorry
