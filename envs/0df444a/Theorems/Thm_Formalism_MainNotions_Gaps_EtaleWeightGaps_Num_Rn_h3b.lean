-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_h3b
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:43:21.663805+00:00
-- url     : https://prove2.me/theorems/9c14bc08-ce01-4d02-9ac3-b45341e5a811
-- title:
--   Rn: h3b
-- statement:
--   The Rn construction uses the h3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L303-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L303-L324

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3b {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) :
    TO * (1250 * r) * rd ^ 2 * PP * d ^ 2 ≤ q := by sorry
