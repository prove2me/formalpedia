-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticNormalizedCoefficientMap_zero
-- name    : ClassicalComplexWPT.analyticNormalizedCoefficientMap_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:44.520839+00:00
-- url     : https://prove2.me/theorems/cb0187d3-c121-4275-87a5-4bb36dbda580
-- title:
--   Classical Complex WPT: analytic Normalized Coefficient Map zero
-- statement:
--   The Classical Complex WPT construction uses the analytic Normalized Coefficient Map zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L291-L312
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L291-L312

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

theorem ClassicalComplexWPT.analyticNormalizedCoefficientMap_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    analyticNormalizedCoefficientMap p r hr d 0 = normalizedOriginCoeffs p r hr d := by sorry
