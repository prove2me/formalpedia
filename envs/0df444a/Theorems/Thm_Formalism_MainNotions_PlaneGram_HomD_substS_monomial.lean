-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_substS_monomial
-- name    : Formalism.MainNotions.PlaneGram.HomD_substS_monomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:03:03.011315+00:00
-- url     : https://prove2.me/theorems/41c81480-157e-4cdb-85c1-a21e1f291309
-- title:
--   Plane Gram: Hom D subst S monomial
-- statement:
--   The Plane Gram construction uses the Hom D subst S monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L735-L755
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L735-L755

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

theorem Formalism.MainNotions.PlaneGram.HomD_substS_monomial (α : L × Fin r →₀ ℕ) :
    HomD (ldeg α) (substS ι sg S A B (monomial α 1)) := by sorry
