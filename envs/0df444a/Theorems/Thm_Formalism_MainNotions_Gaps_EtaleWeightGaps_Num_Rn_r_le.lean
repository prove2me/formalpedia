-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_r_le
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.r_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:11.650738+00:00
-- url     : https://prove2.me/theorems/a5168f2f-ad84-4c0f-bf4d-f1a5bb832720
-- title:
--   Rn: r le
-- statement:
--   The Rn construction uses the r le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L301-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L301-L301

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
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.r_le : r ≤ k ^ 2 := by sorry
