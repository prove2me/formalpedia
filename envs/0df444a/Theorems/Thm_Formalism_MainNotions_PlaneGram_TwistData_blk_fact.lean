-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_blk_fact
-- name    : Formalism.MainNotions.PlaneGram.TwistData.blk_fact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:04:45.558865+00:00
-- url     : https://prove2.me/theorems/24ede493-72ad-46e9-b7a0-fc58db5cde6d
-- title:
--   Twist Data: blk fact
-- statement:
--   The Twist Data construction uses the blk fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L101-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L101-L115

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

theorem Formalism.MainNotions.PlaneGram.TwistData.blk_fact (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ ζ' : D.EM} (h : D.GoodE p ζ) (hb : D.SameBlockAlt ζ ζ') :
    vN v (fact ζ') - vN v (fact ζ) ≤ D.kapD p := by sorry
