-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_eIn
-- name    : Formalism.MainNotions.PlaneGram.eIn_eIn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:00.401868+00:00
-- url     : https://prove2.me/theorems/364fce78-db4c-5d50-a93a-01ae0eb91fe7
-- title:
--   Plane Gram: e In e In
-- statement:
--   The Plane Gram construction uses the e In e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L195-L196

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

theorem Formalism.MainNotions.PlaneGram.eIn_eIn (α : L × Fin r →₀ ℕ) : eIn out (eIn out α) = eIn out α := by sorry
