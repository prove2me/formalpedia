-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_rd_pow_le
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.rd_pow_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:48.164739+00:00
-- url     : https://prove2.me/theorems/fcedf1cc-663f-41ba-810f-e8b4f8c1341c
-- title:
--   Bs: rd pow le
-- statement:
--   The Bs construction uses the rd pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L77-L78

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.rd_pow_le {n : ℕ} (hn : n ≤ 8) : rd ^ n ≤ sb := by sorry
