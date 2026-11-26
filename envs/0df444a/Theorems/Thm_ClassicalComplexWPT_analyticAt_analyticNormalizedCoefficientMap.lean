-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_analyticNormalizedCoefficientMap
-- name    : ClassicalComplexWPT.analyticAt_analyticNormalizedCoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:36.047351+00:00
-- url     : https://prove2.me/theorems/b506a196-745a-57c5-ba75-d4955455a1ed
-- title:
--   Classical Complex WPT: analytic At analytic Normalized Coefficient Map
-- statement:
--   The Classical Complex WPT construction uses the analytic At analytic Normalized Coefficient Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L314-L319
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L314-L319

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_analyticNormalizedCoefficientMap {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 := by sorry
