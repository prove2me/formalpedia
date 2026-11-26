-- Prove2me | Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_top_ne_zero
-- name    : ClassicalComplexWPT.originWeightedCoeffs_top_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:27.376837+00:00
-- url     : https://prove2.me/theorems/0d92b858-7ebb-4230-bf5a-7a74884a23e1
-- title:
--   Classical Complex WPT: origin Weighted Coeffs top ne zero
-- statement:
--   The Classical Complex WPT construction uses the origin Weighted Coeffs top ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L183-L193
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L183-L193

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

theorem ClassicalComplexWPT.originWeightedCoeffs_top_ne_zero {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (R : ℝ≥0) (hR0 : 0 < R)
    (hR : (R : ℝ≥0∞) < p.radius) :
    originWeightedCoeffs p R hR d ≠ 0 := by sorry
