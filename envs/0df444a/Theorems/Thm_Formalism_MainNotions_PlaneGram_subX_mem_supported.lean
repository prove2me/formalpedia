-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_subX_mem_supported
-- name    : Formalism.MainNotions.PlaneGram.subX_mem_supported
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:07:48.492111+00:00
-- url     : https://prove2.me/theorems/c45eb022-4bc9-4eac-9a99-283932f250cf
-- title:
--   Plane Gram: sub X mem supported
-- statement:
--   The Plane Gram construction uses the sub X mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L280-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L280-L292

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
variable (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.subX_mem_supported (x : L × Fin r) (hx : ¬ out x.1) :
    subX sg S A B x ∈ supported R {y : L × Fin r | ¬ out y.1} := by sorry
