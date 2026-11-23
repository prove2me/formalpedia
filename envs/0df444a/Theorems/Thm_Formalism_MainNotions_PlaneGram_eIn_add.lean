-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_add
-- name    : Formalism.MainNotions.PlaneGram.eIn_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:50.857218+00:00
-- url     : https://prove2.me/theorems/dc2903e1-db56-43b0-801b-e3c37743cf2d
-- title:
--   Plane Gram: e In add
-- statement:
--   The Plane Gram construction uses the e In add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L189-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L189-L190

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

theorem Formalism.MainNotions.PlaneGram.eIn_add (α β : L × Fin r →₀ ℕ) : eIn out (α + β) = eIn out α + eIn out β := by sorry
