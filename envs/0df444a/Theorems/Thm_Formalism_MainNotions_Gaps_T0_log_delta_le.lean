-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_log_delta_le
-- name    : Formalism.MainNotions.Gaps.T0.log_delta_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:37.851791+00:00
-- url     : https://prove2.me/theorems/273a760c-0861-4af0-85ad-91a74810f28a
-- title:
--   T0: log delta le
-- statement:
--   The T0 construction uses the log delta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L420-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L420-L423

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

theorem Formalism.MainNotions.Gaps.T0.log_delta_le {R δ d Pd : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hRδ : R * δ ≤ d) (hd : Real.log d ≤ Pd) :
    Real.log δ ≤ Pd := by sorry
