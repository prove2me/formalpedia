-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costM_choose
-- name    : Formalism.MainNotions.PlaneGram.TwistData.costM_choose
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:46:55.931929+00:00
-- url     : https://prove2.me/theorems/4b894c90-f978-5b13-b9bc-04cfbaeea373
-- title:
--   Twist Data: cost M choose
-- statement:
--   The Twist Data construction uses the cost M choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L56-L58

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

theorem Formalism.MainNotions.PlaneGram.TwistData.costM_choose [NeZero D.r] (hV2 : V2 K) (x : D.ML × Fin D.r) (k : ℕ) :
    CostV (K := K) D.msg Set.univ k (fun ζ => ((ζ x).choose k : K)) := by sorry
