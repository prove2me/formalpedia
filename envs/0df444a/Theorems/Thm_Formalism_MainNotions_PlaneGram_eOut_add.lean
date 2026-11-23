-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add
-- name    : Formalism.MainNotions.PlaneGram.eOut_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:02.606499+00:00
-- url     : https://prove2.me/theorems/a8ab0a8e-36bb-4214-af84-6e5eeda2fc63
-- title:
--   Plane Gram: e Out add
-- statement:
--   The Plane Gram construction uses the e Out add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L186-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L186-L187

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

theorem Formalism.MainNotions.PlaneGram.eOut_add (α β : L × Fin r →₀ ℕ) : eOut out (α + β) = eOut out α + eOut out β := by sorry
