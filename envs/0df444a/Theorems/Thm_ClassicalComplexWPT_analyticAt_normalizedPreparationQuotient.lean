-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationQuotient
-- name    : ClassicalComplexWPT.analyticAt_normalizedPreparationQuotient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:04.944164+00:00
-- url     : https://prove2.me/theorems/49159e9a-c046-5bcf-800c-7a61c7eecc22
-- title:
--   Classical Complex WPT: analytic At normalized Preparation Quotient
-- statement:
--   The Classical Complex WPT construction uses the analytic At normalized Preparation Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L49-L57
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L49-L57

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_normalizedPreparationQuotient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 := by sorry
