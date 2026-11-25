-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_HF_le
-- name    : Formalism.MainNotions.Gaps.T0.HF_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:02.736088+00:00
-- url     : https://prove2.me/theorems/ef6cf7ab-bfab-4b8d-8231-2d8b4793df31
-- title:
--   T0: HF le
-- statement:
--   The T0 construction uses the HF le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L446-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L446-L464

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

theorem Formalism.MainNotions.Gaps.T0.HF_le {HL HF δ D G PH PI4 Prw L aG2 w : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hw0 : 0 ≤ w) (hw : w ≤ Prw * L) (hP : PI4 + Prw ≤ PH)
    (ha : aG2 ≤ 4 / 3 * (D + 4) * δ) (hHL : HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L)
    (hH : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * w) :
    HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L := by sorry
