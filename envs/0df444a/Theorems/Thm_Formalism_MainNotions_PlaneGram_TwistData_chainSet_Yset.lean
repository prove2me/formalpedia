-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_chainSet_Yset
-- name    : Formalism.MainNotions.PlaneGram.TwistData.chainSet_Yset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:04:39.227028+00:00
-- url     : https://prove2.me/theorems/afc2766d-9f09-4fb3-8c34-ca6ae3eb7ffd
-- title:
--   Twist Data: chain Set Yset
-- statement:
--   The Twist Data construction uses the chain Set Yset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L128-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L128-L159

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

theorem Formalism.MainNotions.PlaneGram.TwistData.chainSet_Yset (hch : ∀ j i, D.chain j i ⊆ D.LLj j) (j : Fin D.J) (i : Fin (D.nch j))
    (j' : Fin D.J) (m : Fin D.r) :
    D.chainSet j i ⊆ D.Yset j' m ∨ Disjoint (D.chainSet j i) (D.Yset j' m) := by sorry
