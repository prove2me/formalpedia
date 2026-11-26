-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationCoefficient
-- name    : ClassicalComplexWPT.analyticAt_preparationCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:10:49.389702+00:00
-- url     : https://prove2.me/theorems/2f833d14-3fbe-5a96-bcff-4c11a4e8668e
-- title:
--   Classical Complex WPT: analytic At preparation Coefficient
-- statement:
--   The Classical Complex WPT construction uses the analytic At preparation Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L63-L75
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L63-L75

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

theorem ClassicalComplexWPT.analyticAt_preparationCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hq : AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0)
    (i : Fin d) : AnalyticAt ℂ (preparationCoefficient p r hr d i) 0 := by sorry
