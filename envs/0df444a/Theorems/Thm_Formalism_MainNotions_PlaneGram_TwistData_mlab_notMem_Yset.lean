-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mlab_notMem_Yset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mlab_notMem_Yset
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:42.469032+00:00
-- url     : https://prove2.me/theorems/f1c59966-4a28-42ce-ac7b-685f8d0922f4
-- title:
--   Twist Data: mlab not Mem Yset
-- statement:
--   The Twist Data construction uses the mlab not Mem Yset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L30-L32

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.mlab_notMem_Yset (j : Fin D.J) (m : Fin D.r) (t : D.Tau) : D.mlab t ∉ D.Yset j m := by sorry
