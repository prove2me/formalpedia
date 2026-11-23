-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_add
-- name    : Formalism.MainNotions.PlaneGram.toR_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:56.079624+00:00
-- url     : https://prove2.me/theorems/1af22e47-68b6-4030-91f1-edcef7349e13
-- title:
--   Plane Gram: to R add
-- statement:
--   The Plane Gram construction uses the to R add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L905-L913
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L905-L913

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

theorem Formalism.MainNotions.PlaneGram.toR_add (x y : WithTop ℤ) : toR (x + y) = toR x + toR y := by sorry
