-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_kl_ge
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.kl_ge
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:05.374588+00:00
-- url     : https://prove2.me/theorems/b7e164d4-9381-407a-8606-c218d9b66777
-- title:
--   Rn: kl ge
-- statement:
--   The Rn construction uses the kl ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L113-L117

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.kl_ge : b ≤ D2 * nW + 2 * r + (TO + D2) * q0 := by sorry
