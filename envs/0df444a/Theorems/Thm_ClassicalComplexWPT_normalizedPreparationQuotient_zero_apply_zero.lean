-- Prove2me | Theorems.Thm_ClassicalComplexWPT_normalizedPreparationQuotient_zero_apply_zero
-- name    : ClassicalComplexWPT.normalizedPreparationQuotient_zero_apply_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:41.507386+00:00
-- url     : https://prove2.me/theorems/ba834898-cf1d-4c10-8aa5-34fb9e97aeaa
-- title:
--   Classical Complex WPT: normalized Preparation Quotient zero apply zero
-- statement:
--   The Classical Complex WPT construction uses the normalized Preparation Quotient zero apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L186-L204
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L186-L204

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.normalizedPreparationQuotient_zero_apply_zero {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    normalizedPreparationQuotient p r hr d 0 0 = 1 := by sorry
