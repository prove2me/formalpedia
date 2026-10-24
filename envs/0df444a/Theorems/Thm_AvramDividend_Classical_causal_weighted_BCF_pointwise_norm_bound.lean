-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_pointwise_norm_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_pointwise_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:06:04.687063+00:00
-- url     : https://prove2.me/theorems/9ab471fc-1507-4c1f-b0be-c8e42a39a554
-- title:
--   The reweighted causal input is bounded pointwise by its BCF norm
-- statement:
--   The positive exponential and its reciprocal cancel exactly, so every real-time value of the reweighted extension has weighted absolute value no greater than the supremum norm of f. This converts the finite-horizon sup estimate for the Volterra convolution into a uniform BCF operator norm bound.
-- source:
--   Real.exp_add and BoundedContinuousFunction.norm_coe_le_norm.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_pointwise_norm_bound
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w x : ℝ) :
    Real.exp (-(w * x)) *
      |Real.exp (w * x) * f ⟨max x 0, le_max_right x 0⟩| ≤ ‖f‖ := by sorry
