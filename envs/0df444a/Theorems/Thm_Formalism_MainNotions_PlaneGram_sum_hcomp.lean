-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_sum_hcomp
-- name    : Formalism.MainNotions.PlaneGram.sum_hcomp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:08:03.359631+00:00
-- url     : https://prove2.me/theorems/cd3dddd1-32cf-4b5c-a23c-e63850a392e0
-- title:
--   Plane Gram: sum hcomp
-- statement:
--   The Plane Gram construction uses the sum hcomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L831-L844
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L831-L844

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

theorem Formalism.MainNotions.PlaneGram.sum_hcomp (F : MvPolynomial (L × Fin r) K) :
    F = ∑ d ∈ F.support.image (fun α i => ldeg α i), hcomp d F := by sorry
