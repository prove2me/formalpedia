-- Prove2me | Theorems.Thm_ClassicalComplexWPT_scaleSeq_originWeightedCoeffs
-- name    : ClassicalComplexWPT.scaleSeq_originWeightedCoeffs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:14.71482+00:00
-- url     : https://prove2.me/theorems/38c79241-b783-5dcb-b51c-982785ca0e28
-- title:
--   Classical Complex WPT: scale Seq origin Weighted Coeffs
-- statement:
--   The Classical Complex WPT construction uses the scale Seq origin Weighted Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L202-L212
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/NormalizedCoefficients.lean#L202-L212

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

theorem ClassicalComplexWPT.scaleSeq_originWeightedCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R t : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (ht : t ≤ 1) :
    scaleSeq t ht (originWeightedCoeffs p R hR) =
      originWeightedCoeffs p (t * R) (mul_radius_lt_of_le_one p R t hR ht) := by sorry
