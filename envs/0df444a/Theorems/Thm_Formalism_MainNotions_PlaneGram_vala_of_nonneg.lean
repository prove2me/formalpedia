-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_of_nonneg
-- name    : Formalism.MainNotions.PlaneGram.vala_of_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:53.800624+00:00
-- url     : https://prove2.me/theorems/2b5a4467-c28e-410f-91af-b9d2c4410fca
-- title:
--   Plane Gram: vala of nonneg
-- statement:
--   The Plane Gram construction uses the vala of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L972-L973
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L972-L973

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}

theorem Formalism.MainNotions.PlaneGram.vala_of_nonneg {F : MvPolynomial (L × Fin r) K} (h : 0 ≤ valS sg S F) : vala sg S 0 F := by sorry
