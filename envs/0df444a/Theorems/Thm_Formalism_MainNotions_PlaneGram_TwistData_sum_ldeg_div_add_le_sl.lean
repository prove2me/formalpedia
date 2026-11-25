-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_sum_ldeg_div_add_le_sl
-- name    : Formalism.MainNotions.PlaneGram.TwistData.sum_ldeg_div_add_le_sl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:27.052807+00:00
-- url     : https://prove2.me/theorems/1cd1ec75-665b-494e-96dc-918c3fe705fa
-- title:
--   Twist Data: sum ldeg div add le sl
-- statement:
--   The Twist Data construction uses the sum ldeg div add le sl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L272-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L272-L306

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

theorem Formalism.MainNotions.PlaneGram.TwistData.sum_ldeg_div_add_le_sl (D : TwistData K) (p : ℕ) (hp : 0 < p) (hr : 0 < D.r) (hH : D.HypH p 13) (M : D.EA)
    (hMd : ∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) (j : Fin D.J) (i : Fin (D.nch j)) :
    (∑ t : D.Tau, (if t.1 = D.aux₃ j then (ldeg M (Sum.inr t) : ℝ) / (D.P p t : ℝ) + D.c else 0)) +
      12 * D.c ≤ D.sl j i := by sorry
