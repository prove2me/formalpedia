-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eIn
-- name    : Formalism.MainNotions.PlaneGram.eOut_eIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:50.000305+00:00
-- url     : https://prove2.me/theorems/2a38618f-53cf-4a4b-a0ba-94039c5a329f
-- title:
--   Plane Gram: e Out e In
-- statement:
--   The Plane Gram construction uses the e Out e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L201-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L201-L202

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
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.eOut_eIn (α : L × Fin r →₀ ℕ) : eOut out (eIn out α) = 0 := by sorry
