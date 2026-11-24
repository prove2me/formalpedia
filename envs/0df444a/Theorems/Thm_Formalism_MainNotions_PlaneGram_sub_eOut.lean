-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_sub_eOut
-- name    : Formalism.MainNotions.PlaneGram.sub_eOut
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:08:00.461701+00:00
-- url     : https://prove2.me/theorems/71b3bc5a-1649-4667-a096-82c9de22e0ce
-- title:
--   Plane Gram: sub e Out
-- statement:
--   The Plane Gram construction uses the sub e Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L217-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L217-L218

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

theorem Formalism.MainNotions.PlaneGram.sub_eOut (α : L × Fin r →₀ ℕ) : α - eOut out α = eIn out α := by sorry
