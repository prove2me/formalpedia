-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_eIn_apply_mb
-- name    : Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:04:56.790429+00:00
-- url     : https://prove2.me/theorems/ba779896-8575-4a37-b9af-cb06b444d23c
-- title:
--   Twist Data: e In apply mb
-- statement:
--   The Twist Data construction uses the e In apply mb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L13-L15

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

theorem Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mb (ζ : D.EM) (b : D.Lb) (a : Fin D.r) : eIn D.outP ζ (D.mb b, a) = ζ (D.mb b, a) := by sorry
