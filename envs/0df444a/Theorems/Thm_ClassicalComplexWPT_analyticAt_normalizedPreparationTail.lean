-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationTail
-- name    : ClassicalComplexWPT.analyticAt_normalizedPreparationTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:58.683116+00:00
-- url     : https://prove2.me/theorems/c5eae068-c6ac-5e36-8ffe-57602f302609
-- title:
--   Classical Complex WPT: analytic At normalized Preparation Tail
-- statement:
--   The Classical Complex WPT construction uses the analytic At normalized Preparation Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L43-L47
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L43-L47

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_normalizedPreparationTail {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (normalizedPreparationTail p r hr d) 0 := by sorry
