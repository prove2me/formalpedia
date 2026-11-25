-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_support_hcomp_subset
-- name    : Formalism.MainNotions.PlaneGram.support_hcomp_subset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:53.939555+00:00
-- url     : https://prove2.me/theorems/7478c73b-81f7-512b-bde6-d34012fc917f
-- title:
--   Plane Gram: support hcomp subset
-- statement:
--   The Plane Gram construction uses the support hcomp subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L822-L829
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L822-L829

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

theorem Formalism.MainNotions.PlaneGram.support_hcomp_subset (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    (hcomp d F).support ⊆ F.support := by sorry
