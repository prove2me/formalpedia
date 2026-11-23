-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_IntervalBounds_basics
-- name    : Formalism.CountingSumsFrames.IntervalBounds.basics
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:34.918737+00:00
-- url     : https://prove2.me/theorems/f00809c4-1ecb-4ad6-b774-0a81bdfedc1b
-- title:
--   Interval Bounds: basics
-- statement:
--   The Interval Bounds construction uses the basics property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L16-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L16-L104

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_ApolarComparisonExponent
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound
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
open Formalism.CountingSumsFrames.IntervalBounds
open ParamsIProof

theorem Formalism.CountingSumsFrames.IntervalBounds.basics (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ)
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (h : PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar) :
    (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ (5 : ℝ) ≤ k ∧ (1 : ℝ) ≤ J ∧ (J : ℝ) ≤ N ∧ (25 : ℝ) ≤ p ∧
    1 ≤ (p : ℝ) ^ G' ∧ 0 < a ∧ 1 ≤ Real.log a ∧ 1 ≤ Real.logb p a ∧ 0 ≤ logBaseP p a k ∧
    logBaseP p a k ≤ 3 * Real.logb p a ∧ 1 ≤ logScale C₀ N₁ a ∧ (N : ℝ) ≤ k ∧ (N₁ : ℝ) ^ 2 ≤ k ∧
    0 ≤ D ∧ 1 ≤ b' := by sorry
