-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_goodE_splitE
-- name    : Formalism.MainNotions.PlaneGram.TwistData.goodE_splitE
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:53.568261+00:00
-- url     : https://prove2.me/theorems/b9aea83e-3e3b-40c8-b325-6d6126bbcae7
-- title:
--   Twist Data: good E split E
-- statement:
--   The Twist Data construction uses the good E split E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L309-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L309-L332

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
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
variable (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.goodE_splitE {p : ℕ} (hp : 0 < p) {ζ : D.EM} (hw : ∀ t a, ζ (D.mw t, a) = 0)
    (hpost : ∀ j, D.PostE j ζ) : D.GoodE p (D.splitE p ζ) := by sorry
