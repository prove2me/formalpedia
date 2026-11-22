-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mw
-- name    : Formalism.MainNotions.PlaneGram.TwistData.splitE_mw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:13.770794+00:00
-- url     : https://prove2.me/theorems/de06251e-79f6-4448-a6be-1b8b3d2d254c
-- title:
--   Twist Data: split E mw
-- statement:
--   The Twist Data construction uses the split E mw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L269-L271

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
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
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.splitE_mw (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mw t, a) = ζ (D.mw t, a) + ζ (D.mlab t, a) / D.P p t := by sorry
