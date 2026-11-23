-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_IntervalBounds_log_size_bound_le
-- name    : Formalism.CountingSumsFrames.IntervalBounds.log_size_bound_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:27.412292+00:00
-- url     : https://prove2.me/theorems/db87c442-964c-4a54-aeb4-109abc5cd72c
-- title:
--   Interval Bounds: log size bound le
-- statement:
--   The Interval Bounds construction uses the log size bound le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L106-L109

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

theorem Formalism.CountingSumsFrames.IntervalBounds.log_size_bound_le (k lg kap1 : ℝ) (hk : 1 ≤ k) (hlg : 0 ≤ lg) (h : kap1 ≤ (k - 1) ^ 2 * lg) :
    kap1 ≤ k ^ 2 * lg := by sorry
