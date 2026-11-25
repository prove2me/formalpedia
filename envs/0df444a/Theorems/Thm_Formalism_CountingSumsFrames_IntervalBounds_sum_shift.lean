-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_IntervalBounds_sum_shift
-- name    : Formalism.CountingSumsFrames.IntervalBounds.sum_shift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:23:17.819889+00:00
-- url     : https://prove2.me/theorems/bf56ad62-302c-41bb-b5be-af65f30efe8e
-- title:
--   Interval Bounds: sum shift
-- statement:
--   The Interval Bounds construction uses the sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/IntervalCleanDepthBound.lean#L111-L119

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

theorem Formalism.CountingSumsFrames.IntervalBounds.sum_shift {ι : Type} (T : Finset ι) (f g : ι → ℝ) (e Nr : ℝ) (he : 0 ≤ e)
    (hT : (T.card : ℝ) ≤ Nr) (h : ∀ y ∈ T, f y ≤ g y + e) :
    ∑ y ∈ T, f y ≤ ∑ y ∈ T, g y + Nr * e := by sorry
