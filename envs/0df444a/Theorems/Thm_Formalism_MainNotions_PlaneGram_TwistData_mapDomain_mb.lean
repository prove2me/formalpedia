-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mapDomain_mb
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:05:09.222801+00:00
-- url     : https://prove2.me/theorems/1d21a4dc-f7d6-42b7-a5c1-bb2fd0f59684
-- title:
--   Twist Data: map Domain mb
-- statement:
--   The Twist Data construction uses the map Domain mb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L67-L69

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

theorem Formalism.MainNotions.PlaneGram.TwistData.mapDomain_mb (α : D.EA) (b : D.Lb) (a : Fin D.r) :
    (α.mapDomain (Prod.map D.iotaL id)) (D.mb b, a) = α (Sum.inl b, a) := by sorry
