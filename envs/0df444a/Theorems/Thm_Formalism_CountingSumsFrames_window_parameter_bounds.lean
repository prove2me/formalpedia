-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
-- name    : Formalism.CountingSumsFrames.window_parameter_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:47.254079+00:00
-- url     : https://prove2.me/theorems/7af47276-fac9-4fad-8093-00c0a9e808db
-- title:
--   Counting Sums Frames: window parameter bounds
-- statement:
--   The Counting Sums Frames construction uses the window parameter bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L10-L18

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

theorem Formalism.CountingSumsFrames.window_parameter_bounds {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r : ℝ) + 1) ^ 2 * Y ^ 2 ≤ p ∧ ((r : ℝ) + 1) * Y ^ 2 * Real.log a ≤ a / b' ∧
    (N : ℝ) ≤ (r : ℝ) + 1 ∧ (N₁ : ℝ) ^ 4 ≤ (r : ℝ) + 1 ∧ Real.log a ≤ (r : ℝ) + 1 ∧ 0 ≤ La ∧
    La ≤ (r : ℝ) + 1 ∧ ((r : ℝ) + 1) ^ 3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p : ℝ) < a / b' ∧
    (3 : ℝ) ≤ (r : ℝ) + 1 ∧ (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ 1 ≤ Q ∧ 0 < b' := by sorry
