-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_eval_weightedCoefficientSeries
-- name    : ClassicalComplexWPT.analyticAt_eval_weightedCoefficientSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:51.248916+00:00
-- url     : https://prove2.me/theorems/e137f020-43c1-5240-b9e0-6dd8ff775076
-- title:
--   Classical Complex WPT: analytic At eval weighted Coefficient Series
-- statement:
--   The weighted coefficient family can be evaluated analytically in the base
--   and distinguished variables.  This is the specialization of
--   `AnalyticAt.evalL1PowerSeries` used for analytic quotients and units.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L68-L75
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L68-L75

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_eval_weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hrp : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (fun x : Base n × ℂ ↦
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum x.1)
        ((r : ℂ)⁻¹ * x.2)) 0 := by sorry
