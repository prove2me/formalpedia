-- Prove2me | Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_low_eq_zero
-- name    : ClassicalComplexWPT.originWeightedCoeffs_low_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:14.287713+00:00
-- url     : https://prove2.me/theorems/e8e67f22-a317-4c2f-83cc-8f6b814077a7
-- title:
--   Classical Complex WPT: origin Weighted Coeffs low eq zero
-- statement:
--   The Classical Complex WPT construction uses the origin Weighted Coeffs low eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L174-L181
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L174-L181

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

theorem ClassicalComplexWPT.originWeightedCoeffs_low_eq_zero {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) {k : ℕ} (hk : k < d) :
    originWeightedCoeffs p R hR k = 0 := by sorry
