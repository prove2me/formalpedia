-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_log_seg_le_four_logb
-- name    : Formalism.CountingSumsFrames.log_seg_le_four_logb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:48:17.623478+00:00
-- url     : https://prove2.me/theorems/ef6e550c-d178-4c11-b208-e6c024283058
-- title:
--   Counting Sums Frames: log seg le four logb
-- statement:
--   The Counting Sums Frames construction uses the log seg le four logb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L73-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L73-L86

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

theorem Formalism.CountingSumsFrames.log_seg_le_four_logb {p r : ℕ} {a : ℝ} (hp : (9 : ℝ) ≤ p) (hpa : (p : ℝ) < a) (hr : (r : ℝ) ≤ a) :
    0 ≤ lgSeg p a r ∧ lgSeg p a r ≤ 4 * Real.logb p a := by sorry
