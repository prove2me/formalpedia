-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_polyA
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.polyA
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:49:33.34274+00:00
-- url     : https://prove2.me/theorems/544d266a-0f63-432a-adfd-192ab54f5a1e
-- title:
--   Num: poly A
-- statement:
--   The Num construction uses the poly A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L376-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L376-L396

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.polyA {Z PP tableDegreeThreeBase PO lk Dp : ℝ} (hZ : 10 ^ 60 ≤ Z) (hPP : Z ^ 12 ≤ PP) (hP0 : tableDegreeThreeBase ≤ 30 * Z)
    (hPO : PO ≤ 217 * Z ^ 2) (hl1 : 1 ≤ lk) (hl : lk ≤ 6 * Z) (hD : 1 ≤ Dp) :
    (2 * 0 + 1 / 2 + tableDegreeThreeBase * lk + 3 / 2 * (Z * lk + PO) ≤ PP) ∧
    (60 * 0 + 180 * (1 / 2) + 44 * (2 * 0 + 1 / 2 + tableDegreeThreeBase * lk + 3 / 2 * (Z * lk + PO)) + 22 * (2 * Z) ≤ PP ^ 2 * Dp) := by sorry
