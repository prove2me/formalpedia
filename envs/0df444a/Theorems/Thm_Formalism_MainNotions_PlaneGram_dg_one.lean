-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_one
-- name    : Formalism.MainNotions.PlaneGram.dg_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:12.599732+00:00
-- url     : https://prove2.me/theorems/256cdf4c-7e79-4342-a171-5d37bbe90160
-- title:
--   Plane Gram: dg one
-- statement:
--   The Plane Gram construction uses the dg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1143-L1144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1143-L1144

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
variable {K : Type} [Field K]

theorem Formalism.MainNotions.PlaneGram.dg_one {σ : Type} (F : MvPolynomial σ K) : dg (fun _ => (1 : K)) F = F := by sorry
