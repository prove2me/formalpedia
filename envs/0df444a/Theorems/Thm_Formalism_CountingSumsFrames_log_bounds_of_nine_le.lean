-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_log_bounds_of_nine_le
-- name    : Formalism.CountingSumsFrames.log_bounds_of_nine_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:04.932001+00:00
-- url     : https://prove2.me/theorems/a82bce0d-4cec-485d-b86f-5f0c429b3282
-- title:
--   Counting Sums Frames: log bounds of nine le
-- statement:
--   The Counting Sums Frames construction uses the log bounds of nine le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L58-L71

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.log_bounds_of_nine_le {pp a : ℝ} (hp : 9 ≤ pp) (ha : pp < a) :
    2 ≤ Real.log pp ∧ 1 < Real.logb pp a ∧ 2 ≤ Real.log a := by sorry
