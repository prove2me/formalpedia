-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_disjoint
-- name    : Formalism.MainNotions.PlaneGram.TwistData.chainSet_disjoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:13.237938+00:00
-- url     : https://prove2.me/theorems/af1f0cc4-fa0f-44c6-b701-499f7f45590d
-- title:
--   Twist Data: chain Set disjoint
-- statement:
--   The Twist Data construction uses the chain Set disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L92-L107

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

theorem Formalism.MainNotions.PlaneGram.TwistData.chainSet_disjoint (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j j' : Fin D.J) (hj : j ≠ j')
    (i : Fin (D.nch j)) (i' : Fin (D.nch j')) : Disjoint (D.chainSet j i) (D.chainSet j' i') := by sorry
