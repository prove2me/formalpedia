-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_depth_le_square_bound
-- name    : Formalism.CountingSumsFrames.depth_le_square_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:12.132803+00:00
-- url     : https://prove2.me/theorems/e24fc1a9-83bf-4f5e-9432-6f7104b1dbd1
-- title:
--   Counting Sums Frames: depth le square bound
-- statement:
--   The Counting Sums Frames construction uses the depth le square bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SegmentTopRoomPublished.lean#L127-L135

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

theorem Formalism.CountingSumsFrames.depth_le_square_bound {p N N₁ r s t : ℕ} {Y a : ℝ} (hY : 1 ≤ Y) (hr : (3 : ℝ) ≤ (r : ℝ) + 1)
    (hN1 : (1 : ℝ) ≤ N₁) (hts : t ≤ s) (hs : s ≤ N₁) (hlg : 0 ≤ lgSeg p a r) :
    DjSeg p N r s t Y a ≤
      45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a := by sorry
