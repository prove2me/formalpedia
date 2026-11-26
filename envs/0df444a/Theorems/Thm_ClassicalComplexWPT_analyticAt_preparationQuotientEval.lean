-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationQuotientEval
-- name    : ClassicalComplexWPT.analyticAt_preparationQuotientEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:17.272323+00:00
-- url     : https://prove2.me/theorems/5359efc9-03c6-49f1-a927-6bce6d15bea4
-- title:
--   Classical Complex WPT: analytic At preparation Quotient Eval
-- statement:
--   The Classical Complex WPT construction uses the analytic At preparation Quotient Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L116-L121
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L116-L121

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_preparationQuotientEval {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0) :
    AnalyticAt ℂ (preparationQuotientEval p r hr d) 0 := by sorry
