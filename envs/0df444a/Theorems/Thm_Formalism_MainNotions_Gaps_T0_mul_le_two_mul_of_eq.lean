-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_mul_le_two_mul_of_eq
-- name    : Formalism.MainNotions.Gaps.T0.mul_le_two_mul_of_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:41.286557+00:00
-- url     : https://prove2.me/theorems/2bfd0446-0bd7-4a4b-b5dc-ccf2884b163b
-- title:
--   T0: mul le two mul of eq
-- statement:
--   The T0 construction uses the mul le two mul of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L425-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L425-L426

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0

theorem Formalism.MainNotions.Gaps.T0.mul_le_two_mul_of_eq {κ F' T L : ℝ} (h : κ = F' + T * L - T) (hF : 0 ≤ F') (hT : T ≤ κ) :
    T * L ≤ 2 * κ := by sorry
