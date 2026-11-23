-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eOut
-- name    : Formalism.MainNotions.PlaneGram.eIn_eOut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:51.650816+00:00
-- url     : https://prove2.me/theorems/594af12f-cf07-4074-8972-b2228435563c
-- title:
--   Plane Gram: e In e Out
-- statement:
--   The Plane Gram construction uses the e In e Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L198-L199

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

theorem Formalism.MainNotions.PlaneGram.eIn_eOut (α : L × Fin r →₀ ℕ) : eIn out (eOut out α) = 0 := by sorry
