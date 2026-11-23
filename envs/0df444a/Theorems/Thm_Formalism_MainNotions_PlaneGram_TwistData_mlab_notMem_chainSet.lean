-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_mlab_notMem_chainSet
-- name    : Formalism.MainNotions.PlaneGram.TwistData.mlab_notMem_chainSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:52.02203+00:00
-- url     : https://prove2.me/theorems/df849349-3a15-4772-8f56-95dd77e3a657
-- title:
--   Twist Data: mlab not Mem chain Set
-- statement:
--   The Twist Data construction uses the mlab not Mem chain Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L78-L81

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
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

theorem Formalism.MainNotions.PlaneGram.TwistData.mlab_notMem_chainSet (j : Fin D.J) (i : Fin (D.nch j)) (t : D.Tau) :
    D.mlab t ∉ D.chainSet j i := by sorry
