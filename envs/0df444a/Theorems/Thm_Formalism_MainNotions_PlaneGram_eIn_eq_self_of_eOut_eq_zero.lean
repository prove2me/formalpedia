-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eq_self_of_eOut_eq_zero
-- name    : Formalism.MainNotions.PlaneGram.eIn_eq_self_of_eOut_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:04.458112+00:00
-- url     : https://prove2.me/theorems/3b3e485a-7f07-4e31-a06f-722829114c99
-- title:
--   Plane Gram: e In eq self of e Out eq zero
-- statement:
--   The Plane Gram construction uses the e In eq self of e Out eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L210-L212

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

theorem Formalism.MainNotions.PlaneGram.eIn_eq_self_of_eOut_eq_zero {α : L × Fin r →₀ ℕ} (h : eOut out α = 0) : eIn out α = α := by sorry
