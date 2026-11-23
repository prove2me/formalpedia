-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ne_zero_of_v_eq_zero
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ne_zero_of_v_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:52.046697+00:00
-- url     : https://prove2.me/theorems/b7121ad3-724c-4d9d-b1a0-7cb3a73e681f
-- title:
--   Twist Data: ne zero of v eq zero
-- statement:
--   The Twist Data construction uses the ne zero of v eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L136-L139

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

theorem Formalism.MainNotions.PlaneGram.TwistData.ne_zero_of_v_eq_zero {x : K} (h : v x = 0) : x ≠ 0 := by sorry
