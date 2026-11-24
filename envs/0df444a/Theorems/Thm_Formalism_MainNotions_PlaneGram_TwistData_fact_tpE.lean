-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_tpE
-- name    : Formalism.MainNotions.PlaneGram.TwistData.fact_tpE
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:09.64029+00:00
-- url     : https://prove2.me/theorems/fcfe25d6-04dc-4492-8d66-2d75faec1326
-- title:
--   Twist Data: fact tp E
-- statement:
--   The Twist Data construction uses the fact tp E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L153-L157

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
omit [CharZero K]

theorem Formalism.MainNotions.PlaneGram.TwistData.fact_tpE (ζ : D.EM) : fact (D.tpE ζ) = ∏ t, ∏ a, (ζ (D.mtp t, a)).factorial := by sorry
