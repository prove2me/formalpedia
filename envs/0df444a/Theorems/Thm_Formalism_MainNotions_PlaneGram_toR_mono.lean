-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_mono
-- name    : Formalism.MainNotions.PlaneGram.toR_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:55.47405+00:00
-- url     : https://prove2.me/theorems/37025397-d717-40e3-aa1f-dda023b4da1b
-- title:
--   Plane Gram: to R mono
-- statement:
--   The Plane Gram construction uses the to R mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L895-L903
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L895-L903

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

theorem Formalism.MainNotions.PlaneGram.toR_mono {x y : WithTop ℤ} (h : x ≤ y) : toR x ≤ toR y := by sorry
