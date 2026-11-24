-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_not_labB_of_mem_Yset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.not_labB_of_mem_Yset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:05:20.189081+00:00
-- url     : https://prove2.me/theorems/180d5bec-e595-4fa3-a916-3b7a1a05009a
-- title:
--   Twist Data: not lab B of mem Yset
-- statement:
--   The Twist Data construction uses the not lab B of mem Yset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L354-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L354-L357

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

theorem Formalism.MainNotions.PlaneGram.TwistData.not_labB_of_mem_Yset {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m) :
    ¬ D.labB i = true := by sorry
