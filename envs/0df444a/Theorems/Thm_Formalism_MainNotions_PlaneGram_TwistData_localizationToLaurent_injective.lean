-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_localizationToLaurent_injective
-- name    : Formalism.MainNotions.PlaneGram.TwistData.localizationToLaurent_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:57.447364+00:00
-- url     : https://prove2.me/theorems/caa225ce-56c5-457e-b7dd-1e65218d0e22
-- title:
--   Twist Data: localization To Laurent injective
-- statement:
--   The Twist Data construction uses the localization To Laurent injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L45-L46

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

theorem Formalism.MainNotions.PlaneGram.TwistData.localizationToLaurent_injective : Function.Injective (Prod.map D.iotaL (id : Fin D.r → Fin D.r)) := by sorry
