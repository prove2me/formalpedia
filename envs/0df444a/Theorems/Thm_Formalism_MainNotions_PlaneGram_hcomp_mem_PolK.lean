-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_mem_PolK
-- name    : Formalism.MainNotions.PlaneGram.hcomp_mem_PolK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:20.951991+00:00
-- url     : https://prove2.me/theorems/b6d7eda4-9199-4133-8069-063d5061d06b
-- title:
--   Plane Gram: hcomp mem Pol K
-- statement:
--   The Plane Gram construction uses the hcomp mem Pol K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L806-L811
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L806-L811

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

theorem Formalism.MainNotions.PlaneGram.hcomp_mem_PolK (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) : hcomp d F ∈ PolK K r d := by sorry
