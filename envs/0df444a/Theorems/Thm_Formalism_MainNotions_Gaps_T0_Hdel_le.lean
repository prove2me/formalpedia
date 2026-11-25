-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_Hdel_le
-- name    : Formalism.MainNotions.Gaps.T0.Hdel_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:12.896815+00:00
-- url     : https://prove2.me/theorems/aa90ee3c-2a23-4fc1-ad19-91c8105d8ef0
-- title:
--   T0: Hdel le
-- statement:
--   The T0 construction uses the Hdel le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L431-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L431-L444

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

theorem Formalism.MainNotions.Gaps.T0.Hdel_le {HL Hδ δ D G PH PI4 Prw L aG1 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG1 ≤ 4 / 3 * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : Hδ ≤ HL + (δ * PI4 * D * L + D * aG1 * w)) :
    Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L := by sorry
