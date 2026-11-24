-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_tpE
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ldeg_tpE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:04:57.242916+00:00
-- url     : https://prove2.me/theorems/ecdc6501-adf3-48b2-ac7e-d92c5fac6e4d
-- title:
--   Twist Data: ldeg tp E
-- statement:
--   The Twist Data construction uses the ldeg tp E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L222-L224

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
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.ldeg_tpE (ζ : D.EM) (t : D.Tau) : ldeg (D.tpE ζ) (Sum.inr t) = ldeg ζ (D.mtp t) := by sorry
