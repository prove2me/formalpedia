-- Prove2me | Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
-- name    : ClassicalComplexWPT.originWeightedCoeffs_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:29.404811+00:00
-- url     : https://prove2.me/theorems/065f261a-0371-47b5-aa82-4d262bf61e6f
-- title:
--   Classical Complex WPT: origin Weighted Coeffs apply
-- statement:
--   The Classical Complex WPT construction uses the origin Weighted Coeffs apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L168-L172
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L168-L172

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

theorem ClassicalComplexWPT.originWeightedCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (k : ℕ) :
    originWeightedCoeffs p R hR k =
      (R : ℂ) ^ k * lastTaylorCoefficient p k 0 := by sorry

attribute [defeq] ClassicalComplexWPT.originWeightedCoeffs_apply
