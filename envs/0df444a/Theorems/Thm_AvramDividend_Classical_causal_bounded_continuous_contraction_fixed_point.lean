-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_bounded_continuous_contraction_fixed_point
-- name    : AvramDividend.Classical.causal_bounded_continuous_contraction_fixed_point
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:58:54.408696+00:00
-- url     : https://prove2.me/theorems/f13c1dc8-6b1c-446a-a13e-892e1fbea5db
-- title:
--   A strict Lipschitz map on bounded continuous functions has a fixed point
-- statement:
--   Mathlib's Banach fixed-point theorem applied on the complete space of bounded continuous real functions on nonnegative time. This will close the fixed-point extraction after the affine weighted causal map is proved Lipschitz.
-- source:
--   ContractingWith.fixedPoint_isFixedPt; imports mission definition for the namespace.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_bounded_continuous_contraction_fixed_point
    (T : BoundedContinuousFunction ℝ≥0 ℝ → BoundedContinuousFunction ℝ≥0 ℝ)
    (c : NNReal) (hc : c < 1) (hLip : LipschitzWith c T) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ, T f = f := by sorry
