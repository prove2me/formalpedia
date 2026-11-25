-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_add_half_le_mul
-- name    : Formalism.MainNotions.Gaps.T0.add_half_le_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:13.249683+00:00
-- url     : https://prove2.me/theorems/068bac6e-668b-4b0b-bbb6-18e6eb97c6f2
-- title:
--   T0: add half le mul
-- statement:
--   The T0 construction uses the add half le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L417-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L417-L418

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

theorem Formalism.MainNotions.Gaps.T0.add_half_le_mul {lrw Prw L : ℝ} (h : lrw ≤ Prw * (L - 1)) (hP : 1 / 2 ≤ Prw) :
    lrw + 1 / 2 ≤ Prw * L := by sorry
