-- Prove2me | Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
-- name    : ClassicalComplexWPT.normalizedOriginCoeffs_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:02.432262+00:00
-- url     : https://prove2.me/theorems/1f3bd518-52e3-4a93-9aff-f33e610e1843
-- title:
--   Classical Complex WPT: normalized Origin Coeffs apply
-- statement:
--   The Classical Complex WPT construction uses the normalized Origin Coeffs apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L219-L224
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L219-L224

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

theorem ClassicalComplexWPT.normalizedOriginCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d k : ℕ) :
    normalizedOriginCoeffs p r hr d k =
      (((r : ℂ) ^ d * lastTaylorCoefficient p d 0)⁻¹) *
        ((r : ℂ) ^ k * lastTaylorCoefficient p k 0) := by sorry

attribute [defeq] ClassicalComplexWPT.normalizedOriginCoeffs_apply
