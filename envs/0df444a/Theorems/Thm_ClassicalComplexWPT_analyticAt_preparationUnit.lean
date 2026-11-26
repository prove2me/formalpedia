-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationUnit
-- name    : ClassicalComplexWPT.analyticAt_preparationUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:13:10.015592+00:00
-- url     : https://prove2.me/theorems/68f16eff-3eb5-4661-a393-62279b46aaf8
-- title:
--   Classical Complex WPT: analytic At preparation Unit
-- statement:
--   The Classical Complex WPT construction uses the analytic At preparation Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L130-L140
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L130-L140

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

theorem ClassicalComplexWPT.analyticAt_preparationUnit {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    AnalyticAt ℂ (preparationUnit p r hr d) 0 := by sorry
