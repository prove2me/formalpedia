-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inl
-- name    : Formalism.MainNotions.PlaneGram.TwistData.sum_onLetter_apply_inl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:03.501272+00:00
-- url     : https://prove2.me/theorems/8dfe665b-3088-41c6-bd7e-37670ee40eea
-- title:
--   Twist Data: sum on Letter apply inl
-- statement:
--   The Twist Data construction uses the sum on Letter apply inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L207-L212

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
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
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}

theorem Formalism.MainNotions.PlaneGram.TwistData.sum_onLetter_apply_inl (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (b : D.Lb) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inl b, a) = 0 := by sorry
