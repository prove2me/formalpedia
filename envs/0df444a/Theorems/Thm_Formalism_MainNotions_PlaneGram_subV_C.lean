-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_subV_C
-- name    : Formalism.MainNotions.PlaneGram.subV_C
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:08:29.597366+00:00
-- url     : https://prove2.me/theorems/271f84d8-fa2b-43a4-9c81-cf14938f4f0c
-- title:
--   Plane Gram: sub V C
-- statement:
--   The Plane Gram construction uses the sub V C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L145-L146

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

theorem Formalism.MainNotions.PlaneGram.subV_C (a : K) : subV sg S (C a : MvPolynomial (L × Fin r) K) = C (lauι K r a) := by sorry
