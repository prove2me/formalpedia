-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mtp
-- name    : Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mtp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:05:33.892285+00:00
-- url     : https://prove2.me/theorems/3cdcede3-d544-441a-910e-d3c0fa0a7239
-- title:
--   Twist Data: e In apply mtp
-- statement:
--   The Twist Data construction uses the e In apply mtp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L25-L27

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

theorem Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mtp (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mtp t, a) = 0 := by sorry
