-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationRemainder
-- name    : ClassicalComplexWPT.analyticAt_normalizedPreparationRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:11.120949+00:00
-- url     : https://prove2.me/theorems/6bb806db-6861-5560-99a7-b1da16b2e9d3
-- title:
--   Classical Complex WPT: analytic At normalized Preparation Remainder
-- statement:
--   The Classical Complex WPT construction uses the analytic At normalized Preparation Remainder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L59-L67
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L59-L67

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_normalizedPreparationRemainder {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0 := by sorry
