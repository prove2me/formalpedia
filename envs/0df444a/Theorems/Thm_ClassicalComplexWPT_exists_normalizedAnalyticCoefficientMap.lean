-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_normalizedAnalyticCoefficientMap
-- name    : ClassicalComplexWPT.exists_normalizedAnalyticCoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:26.036804+00:00
-- url     : https://prove2.me/theorems/94c6b987-c491-5d3f-981c-a67d5a6951b2
-- title:
--   Classical Complex WPT: exists normalized Analytic Coefficient Map
-- statement:
--   Exact distinguished order supplies a normalized analytic coefficient map
--   that is within `1/2` of the monomial at the origin and remains within `1` on
--   a neighborhood of the base origin.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L324-L346
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L324-L346

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

theorem ClassicalComplexWPT.exists_normalizedAnalyticCoefficientMap {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 ∧
      ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ < (1 : ℝ) / 2 ∧
      ∀ᶠ z in 𝓝 (0 : Base n),
        ‖analyticNormalizedCoefficientMap p r hr d z - monomialSeq d‖ < 1 := by sorry
