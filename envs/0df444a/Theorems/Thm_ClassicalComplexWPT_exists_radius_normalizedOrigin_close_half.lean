-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_radius_normalizedOrigin_close_half
-- name    : ClassicalComplexWPT.exists_radius_normalizedOrigin_close_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:18.042255+00:00
-- url     : https://prove2.me/theorems/3ed03b5a-dda6-56d3-beff-3cc716768f05
-- title:
--   Classical Complex WPT: exists radius normalized Origin close half
-- statement:
--   The Classical Complex WPT construction uses the exists radius normalized Origin close half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L226-L253
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L226-L253

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

theorem ClassicalComplexWPT.exists_radius_normalizedOrigin_close_half {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
        ‖normalizedOriginCoeffs p r hr d - monomialSeq d‖ < (1 : ℝ) / 2 := by sorry
