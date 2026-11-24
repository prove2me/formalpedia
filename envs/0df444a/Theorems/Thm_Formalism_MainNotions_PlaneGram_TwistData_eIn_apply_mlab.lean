-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mlab
-- name    : Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mlab
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:05:09.689044+00:00
-- url     : https://prove2.me/theorems/40a257d7-0642-4d16-aafd-7f59ce95a373
-- title:
--   Twist Data: e In apply mlab
-- statement:
--   The Twist Data construction uses the e In apply mlab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L21-L23

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
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

theorem Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mlab (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mlab t, a) = 0 := by sorry
