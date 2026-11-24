-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_phE_lower
-- name    : Formalism.MainNotions.PlaneGram.TwistData.fact_phE_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:53.582929+00:00
-- url     : https://prove2.me/theorems/e15ec369-87ba-46cc-996a-87348a937faa
-- title:
--   Twist Data: fact ph E lower
-- statement:
--   The Twist Data construction uses the fact ph E lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L126-L133

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

theorem Formalism.MainNotions.PlaneGram.TwistData.fact_phE_lower (hD : DVRHyp v p) (hr : 1 ≤ D.r) {ζ : D.EM} (h : D.GoodE p ζ) :
    2 * D.n0 v - D.kapD p ≤ vN v (fact (D.phE p ζ)) := by sorry
