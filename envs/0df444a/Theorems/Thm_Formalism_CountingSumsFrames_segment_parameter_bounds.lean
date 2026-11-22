-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds
-- name    : Formalism.CountingSumsFrames.segment_parameter_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:18.697126+00:00
-- url     : https://prove2.me/theorems/b38d6ccc-66a0-4a8e-8b6f-c98b91aac912
-- title:
--   Counting Sums Frames: segment parameter bounds
-- statement:
--   The Counting Sums Frames construction uses the segment parameter bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L102-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentHypOfIntervalHyp.lean#L102-L138

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

theorem Formalism.CountingSumsFrames.segment_parameter_bounds {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r:ℝ)+1)^2 * Y^2 ≤ p ∧ ((r:ℝ)+1) * Y^2 * Real.log a ≤ a / b' ∧ Real.log a ≤ (r:ℝ)+1 ∧
    ((r:ℝ)+1)^3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p:ℝ) < a / b' ∧ (2:ℝ) ≤ r ∧ 1 ≤ Q ∧ 0 < b' ∧ (9:ℝ) ≤ p ∧
    27 ≤ b' ∧ (p:ℝ) * b' < a ∧ 1 ≤ Real.log a ∧ (1:ℝ) ≤ N₁ ∧ (r:ℝ) + 1 ≤ b' := by sorry
