-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_param_cube_le_bound
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.param_cube_le_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:13.978068+00:00
-- url     : https://prove2.me/theorems/553453fa-5e18-4bbe-9f18-e4b2e4bee606
-- title:
--   Bs: param cube le bound
-- statement:
--   The Bs construction uses the param cube le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L71-L75

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.param_cube_le_bound : PP ^ 3 ≤ sb := by sorry
