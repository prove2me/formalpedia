-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mw
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mw
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:04:43.485228+00:00
-- url     : https://prove2.me/theorems/3121e34b-eb27-4ce1-b900-f26962895214
-- title:
--   Twist Data: map Domain mw
-- statement:
--   The Twist Data construction uses the map Domain mw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L75-L79

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

theorem Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mw (α : D.EA) (t : D.Tau) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mw t, a) = 0 := by sorry
