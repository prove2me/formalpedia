-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_toR_coe
-- name    : Formalism.MainNotions.PlaneGram.toR_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:16.685287+00:00
-- url     : https://prove2.me/theorems/9dc47efd-c780-4251-adfe-046ca1d49cbf
-- title:
--   Plane Gram: to R coe
-- statement:
--   The Plane Gram construction uses the to R coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L887-L887
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L887-L887

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

theorem Formalism.MainNotions.PlaneGram.toR_coe (n : ℤ) : toR (n : WithTop ℤ) = (((n : ℤ) : ℝ) : WithTop ℝ) := by sorry
