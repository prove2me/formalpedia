-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_wt_lower
-- name    : Formalism.MainNotions.PlaneGram.TwistData.wt_lower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:37.324605+00:00
-- url     : https://prove2.me/theorems/11f7252d-b8c5-4090-852e-5014ec5677b6
-- title:
--   Twist Data: wt lower
-- statement:
--   The Twist Data construction uses the wt lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L117-L124

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
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
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.wt_lower (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ : D.EM} (h : D.GoodE p ζ) :
    2 * D.n0 v - 2 * D.kapD p ≤ vN v (fact (D.collapseExponent p ζ)) + vN v (fact (D.tpE ζ)) := by sorry
