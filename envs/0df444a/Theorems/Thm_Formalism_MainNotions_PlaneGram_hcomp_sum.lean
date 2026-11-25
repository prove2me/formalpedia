-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_sum
-- name    : Formalism.MainNotions.PlaneGram.hcomp_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:14.764897+00:00
-- url     : https://prove2.me/theorems/c7d5136a-9940-467c-9e2d-3f0da74b538e
-- title:
--   Plane Gram: hcomp sum
-- statement:
--   The Plane Gram construction uses the hcomp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L802-L804
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L802-L804

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

theorem Formalism.MainNotions.PlaneGram.hcomp_sum {κ : Type} (d : L → ℕ) (s : Finset κ) (f : κ → MvPolynomial (L × Fin r) K) :
    hcomp d (∑ k ∈ s, f k) = ∑ k ∈ s, hcomp d (f k) := by sorry
