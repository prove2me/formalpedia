-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_rename_pullL_coefOut
-- name    : Formalism.MainNotions.PlaneGram.TwistData.rename_pullL_coefOut
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:05:42.317864+00:00
-- url     : https://prove2.me/theorems/b2ff8f84-fe8c-4bc8-8307-ac563234e211
-- title:
--   Twist Data: rename pull L coef Out
-- statement:
--   The Twist Data construction uses the rename pull L coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L31-L38

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem Formalism.MainNotions.PlaneGram.TwistData.rename_pullL_coefOut (μ : D.EM) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    rename (Prod.map (D.e0 j) id) (D.pullL j (coefOut (D.outSeg j) μ Z)) = coefOut (D.outSeg j) μ Z := by sorry
