-- Prove2me | Theorems.Thm_ClassicalComplexWPT_normalizedPreparationTail_zero_of_le
-- name    : ClassicalComplexWPT.normalizedPreparationTail_zero_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:19.190267+00:00
-- url     : https://prove2.me/theorems/789eddc2-d33b-4602-baa6-c0f2b7122734
-- title:
--   Classical Complex WPT: normalized Preparation Tail zero of le
-- statement:
--   The Classical Complex WPT construction uses the normalized Preparation Tail zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L111-L132
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L111-L132

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.normalizedPreparationTail_zero_of_le {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius) {k : ℕ} (hk : k ≤ d) :
    normalizedPreparationTail p r hr d 0 k = 0 := by sorry
