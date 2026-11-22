-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
-- name    : Formalism.MainNotions.PlaneGram.eOut_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:58.822784+00:00
-- url     : https://prove2.me/theorems/fc20e115-bc8b-46bc-8d0f-e31493e2aacb
-- title:
--   Plane Gram: e Out apply
-- statement:
--   The Plane Gram construction uses the e Out apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L174-L176

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

theorem Formalism.MainNotions.PlaneGram.eOut_apply (α : L × Fin r →₀ ℕ) (x : L × Fin r) :
    eOut out α x = if out x.1 then α x else 0 := by sorry
