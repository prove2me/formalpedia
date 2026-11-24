-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_of_mem_TLset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.notSegL_of_mem_TLset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:05:42.174509+00:00
-- url     : https://prove2.me/theorems/81d33c56-a8df-460c-b29c-76314baf1c17
-- title:
--   Twist Data: not Seg L of mem TLset
-- statement:
--   The Twist Data construction uses the not Seg L of mem TLset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L114-L120

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

theorem Formalism.MainNotions.PlaneGram.TwistData.notSegL_of_mem_TLset {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.TLset j' m) : ¬ D.SegL j i := by sorry
