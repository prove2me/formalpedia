-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_first_depth_bounds
-- name    : Formalism.CountingSumsFrames.first_depth_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:26.013133+00:00
-- url     : https://prove2.me/theorems/d81ae714-1a71-47b7-b2ff-8ed68957e95a
-- title:
--   Counting Sums Frames: first depth bounds
-- statement:
--   The Counting Sums Frames construction uses the first depth bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L492-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L492-L502

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.first_depth_bounds {t : ℕ} {Y κ : ℝ} (hY : 1 ≤ Y) (hκ : 0 ≤ κ) :
    firstDepth t Y κ ≤ 2 * ((t : ℝ) + 1) * Y * κ ∧ κ ≤ firstDepth t Y κ := by sorry
