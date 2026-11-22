-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_eq_dg
-- name    : Formalism.MainNotions.PlaneGram.hcomp_eq_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:28.906473+00:00
-- url     : https://prove2.me/theorems/4d02e4d5-cc4f-4718-bff1-28b2e025c404
-- title:
--   Plane Gram: hcomp eq dg
-- statement:
--   The Plane Gram construction uses the hcomp eq dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L788-L792
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L788-L792

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

theorem Formalism.MainNotions.PlaneGram.hcomp_eq_dg (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    hcomp d F = dg (fun α => if (∀ i, ldeg α i = d i) then (1 : K) else 0) F := by sorry
