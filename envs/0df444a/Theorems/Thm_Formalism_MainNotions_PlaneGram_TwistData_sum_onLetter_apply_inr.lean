-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_onLetter_apply_inr
-- name    : Formalism.MainNotions.PlaneGram.TwistData.sum_onLetter_apply_inr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:31.603095+00:00
-- url     : https://prove2.me/theorems/dda46867-bfa3-54c3-95cc-47c985ed6ad2
-- title:
--   Twist Data: sum on Letter apply inr
-- statement:
--   The Twist Data construction uses the sum on Letter apply inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L199-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L199-L205

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

theorem Formalism.MainNotions.PlaneGram.TwistData.sum_onLetter_apply_inr (D : TwistData K) (M : D.EA) (s : Finset D.Tau) (t : D.Tau) (a : Fin D.r) :
    (∑ t' ∈ s, onLetter (Sum.inr t' : D.OL) (letE M (Sum.inr t'))) (Sum.inr t, a) =
      if t ∈ s then M (Sum.inr t, a) else 0 := by sorry
