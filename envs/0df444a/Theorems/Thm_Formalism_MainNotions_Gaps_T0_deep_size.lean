-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_deep_size
-- name    : Formalism.MainNotions.Gaps.T0.deep_size
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:37.333467+00:00
-- url     : https://prove2.me/theorems/536195d3-88ba-53b7-88f8-250805ba3d9b
-- title:
--   T0: deep size
-- statement:
--   The T0 construction uses the deep size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L466-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L466-L479

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

theorem Formalism.MainNotions.Gaps.T0.deep_size {T D ΛW Λ0 lrw A E G Prw tableDegreeThreeBase PE L F0 κ : ℝ} (hD : 0 ≤ D) (hDT : D ≤ T) (hG : 0 ≤ G)
    (hPrw : 0 ≤ Prw) (hPE : 0 ≤ PE) (hF0 : 0 ≤ F0) (hκ : 1 ≤ κ) (hTκ : T ≤ κ)
    (hW : ΛW ≤ G * L) (h0 : Λ0 ≤ G * F0) (hrw : lrw ≤ Prw * (L - 1))
    (hn : (T - D) * L + F0 = κ + T - D) (hA : A ≤ tableDegreeThreeBase * κ) (hE : E ≤ PE) :
    (T - D) * (ΛW + lrw) + Λ0 + A + E ≤ (2 * G + Prw + tableDegreeThreeBase + PE) * κ := by sorry
