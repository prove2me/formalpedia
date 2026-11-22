-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds
-- name    : Formalism.CountingSumsFrames.derived_parameter_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:48.185588+00:00
-- url     : https://prove2.me/theorems/c54e1823-74b1-4b06-a1be-fe6fb56f5e56
-- title:
--   Counting Sums Frames: derived parameter bounds
-- statement:
--   The Counting Sums Frames construction uses the derived parameter bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L20-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L20-L56

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

theorem Formalism.CountingSumsFrames.derived_parameter_bounds {K Y a b' Q pp : ℝ} (hY : 1 ≤ Y) (hp : K ^ 2 * Y ^ 2 ≤ pp) (h4 : K ^ 3 * Q * Y ≤ b')
    (hba : b' ≤ a) (h6 : pp < a / b') (hK : 3 ≤ K) (hQ : 1 ≤ Q) (hb0 : 0 < b') :
    9 ≤ pp ∧ 27 ≤ b' ∧ pp * b' < a ∧ 243 < a ∧ pp < a ∧ 9 * (K * Q) ≤ a ∧ K ≤ a ∧
      9 * (K * Q * Y) ≤ a ∧ 3 * (K ^ 2 * Q * Y) ≤ a := by sorry
