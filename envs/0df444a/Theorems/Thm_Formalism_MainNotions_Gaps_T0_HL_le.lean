-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_HL_le
-- name    : Formalism.MainNotions.Gaps.T0.HL_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:06.070653+00:00
-- url     : https://prove2.me/theorems/1e62749b-6913-48c0-a1e0-b274a26076c1
-- title:
--   T0: HL le
-- statement:
--   The T0 construction uses the HL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L517-L568
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L517-L568

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

theorem Formalism.MainNotions.Gaps.T0.HL_le {HL X8 Y HM δ D G PH tableDegreeThreeBase PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw L lrw ΛW Sν DF c cg aδ aG1 : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hL : 1 ≤ L) (hG : 0 ≤ G) (hPP0 : 0 ≤ tableDegreeThreeBase) (hPN : 0 ≤ PN) (hP14 : 0 ≤ tableLineDegreeFive)
    (hP16 : 0 ≤ tableLineDegreeTwo) (hPI : 0 ≤ PI4) (hPrw : 0 ≤ Prw) (hlrw : 0 ≤ lrw) (hw : lrw + 1 / 2 ≤ Prw * L)
    (hPH : tableDegreeThreeBase + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw ≤ PH) (hc1 : c ≤ 1) (hcg0 : 0 ≤ cg) (hcg : cg ≤ 1 / 2)
    (hSν : Sν ≤ PN * L) (hDF : DF ≤ L) (hΛ : ΛW ≤ G * L) (haδ : aδ ≤ 4 / 3 * δ) (haG : aG1 ≤ 4 / 3 * δ)
    (hHM : HM ≤ (D + 1) * δ * (tableDegreeThreeBase * L + ΛW + 1 / 2 * lrw))
    (hX8 : X8 ≤ HM + δ * (Sν + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * cg * aδ * (lrw + 1 / 2))
    (hY : Y ≤ δ * PI4 * D * L + D * aG1 * (lrw + 1 / 2))
    (hHL : HL ≤ 2 * max X8 0 + Y) :
    HL ≤ (D + 1) * δ * (2 * G + 4 * PH) * L := by sorry
