-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_YPset_subset_Yset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.YPset_subset_Yset
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:04:26.079485+00:00
-- url     : https://prove2.me/theorems/c3069914-28f5-4a52-a021-127888201de8
-- title:
--   Twist Data: YPset subset Yset
-- statement:
--   The Twist Data construction uses the YPset subset Yset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L392-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L392-L395

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

theorem Formalism.MainNotions.PlaneGram.TwistData.YPset_subset_Yset (j : Fin D.J) (m : Fin D.r) : D.YPset j m ⊆ D.Yset j m := by sorry
