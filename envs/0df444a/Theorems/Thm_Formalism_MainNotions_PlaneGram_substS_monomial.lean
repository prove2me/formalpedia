-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial
-- name    : Formalism.MainNotions.PlaneGram.substS_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:47.666338+00:00
-- url     : https://prove2.me/theorems/02c90067-d7fa-4054-ad28-1e29a3cf1d7c
-- title:
--   Plane Gram: subst S monomial
-- statement:
--   The Plane Gram construction uses the subst S monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L239-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L239-L243

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)

theorem Formalism.MainNotions.PlaneGram.substS_monomial (α : L × Fin r →₀ ℕ) (c : K) :
    substS ι sg S A B (monomial α c) = C (ι c) * α.prod fun x k => subX sg S A B x ^ k := by sorry
