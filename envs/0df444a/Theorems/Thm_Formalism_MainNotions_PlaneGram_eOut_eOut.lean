-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_eOut
-- name    : Formalism.MainNotions.PlaneGram.eOut_eOut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:00.125795+00:00
-- url     : https://prove2.me/theorems/5fb267cb-e687-4170-8c8a-233184a586f7
-- title:
--   Plane Gram: e Out e Out
-- statement:
--   The Plane Gram construction uses the e Out e Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L192-L193

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

theorem Formalism.MainNotions.PlaneGram.eOut_eOut (α : L × Fin r →₀ ℕ) : eOut out (eOut out α) = eOut out α := by sorry
