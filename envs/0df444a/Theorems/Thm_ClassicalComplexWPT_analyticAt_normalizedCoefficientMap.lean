-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedCoefficientMap
-- name    : ClassicalComplexWPT.analyticAt_normalizedCoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:28.071885+00:00
-- url     : https://prove2.me/theorems/9ebbe908-bc2b-5463-bc21-419fde1561ea
-- title:
--   Classical Complex WPT: analytic At normalized Coefficient Map
-- statement:
--   The Classical Complex WPT construction uses the analytic At normalized Coefficient Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L260-L264
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L260-L264

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

theorem ClassicalComplexWPT.analyticAt_normalizedCoefficientMap {n : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0) :
    AnalyticAt ℂ (normalizedCoefficientMap C denom) 0 := by sorry
