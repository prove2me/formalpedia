-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eval_weightedCoefficientSeries_eq
-- name    : ClassicalComplexWPT.eval_weightedCoefficientSeries_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:41.550506+00:00
-- url     : https://prove2.me/theorems/bbda1f5a-5c62-588a-aefd-fe7b2cc7ae5e
-- title:
--   Classical Complex WPT: eval weighted Coefficient Series eq
-- statement:
--   The Classical Complex WPT construction uses the eval weighted Coefficient Series eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L18-L63
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L18-L63

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eval_weightedCoefficientSeries_eq {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < p.radius)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      p.sum (z, w) := by sorry
