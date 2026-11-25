-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_costA_choose
-- name    : Formalism.MainNotions.PlaneGram.TwistData.costA_choose
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:03.357927+00:00
-- url     : https://prove2.me/theorems/be04e162-539a-5c8a-b494-1633bbd4be64
-- title:
--   Twist Data: cost A choose
-- statement:
--   The Twist Data construction uses the cost A choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L60-L69

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

theorem Formalism.MainNotions.PlaneGram.TwistData.costA_choose [NeZero D.r] (hV2 : V2 K) (x : D.OL × Fin D.r) (k : ℕ) :
    D.CostA p k (fun α => ((α x).choose k : K)) := by sorry
