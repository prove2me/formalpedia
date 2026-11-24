-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_PP_le_sb
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.PP_le_sb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:53.60837+00:00
-- url     : https://prove2.me/theorems/41ff895d-e861-435c-a4ce-d44c3499bb13
-- title:
--   Bs: PP le sb
-- statement:
--   The Bs construction uses the PP le sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L66-L69

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.PP_le_sb : PP ≤ sb := by sorry
