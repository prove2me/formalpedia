-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_eIn_le
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:05:55.651686+00:00
-- url     : https://prove2.me/theorems/5757c77e-2ab0-4de1-8be4-229bc2bf843d
-- title:
--   Twist Data: ldeg e In le
-- statement:
--   The Twist Data construction uses the ldeg e In le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L83-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L83-L97

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

theorem Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn_le {p : ℕ} (hp : 0 < p) {ζ : D.EM} (h : D.GoodE p ζ) (i : D.ML) :
    ldeg (eIn D.outP ζ) i ≤ D.dUp i := by sorry
