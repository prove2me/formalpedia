-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_window_numeric_bound
-- name    : Formalism.CountingSumsFrames.window_numeric_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:48.066797+00:00
-- url     : https://prove2.me/theorems/426ff654-be51-4ccf-9426-23e924836920
-- title:
--   Counting Sums Frames: window numeric bound
-- statement:
--   The Counting Sums Frames construction uses the window numeric bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L395-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L395-L419

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

theorem Formalism.CountingSumsFrames.window_numeric_bound {R Y a P W w : ℝ} (hK : 3 ≤ R + 1) (hY : 1 ≤ Y) (hP : 0 < P) (hW0 : 0 ≤ W)
    (hW : (R + 1) * Y * W ≤ w * a) (hw0 : 0 ≤ w) (hw : w ≤ 5) (h3 : 3 * ((R + 1) ^ 2 * P * Y) ≤ a)
    (h9 : 9 * ((R + 1) * P) ≤ a) :
    0 < a / P - (R + 1) ∧
      R * ((a + W) / P - (a / P - (R + 1))) ≤ (w + 1) / Y * (a / P - (R + 1)) := by sorry
