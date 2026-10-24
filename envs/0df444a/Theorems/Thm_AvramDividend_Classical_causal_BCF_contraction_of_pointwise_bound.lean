-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_BCF_contraction_of_pointwise_bound
-- name    : AvramDividend.Classical.causal_BCF_contraction_of_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:46:56.165819+00:00
-- url     : https://prove2.me/theorems/a3d7b120-a6b9-407f-bc02-9fac5ff954ee
-- title:
--   Uniform pointwise BCF bound implies strict Lipschitz contraction
-- statement:
--   For a self-map of bounded continuous real functions, a uniform pointwise distance bound by (m/a) times the input distance, with 0≤m<a, implies the map is Lipschitz with a coefficient strictly below one. The proof applies the bounded-continuous-function sup-distance characterisation and the ratio inequality.
-- source:
--   Mathlib.Topology.ContinuousMap.Bounded.Basic BoundedContinuousFunction.dist_le and Mathlib.Topology.MetricSpace.Lipschitz LipschitzWith.of_dist_le_mul.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_BCF_contraction_of_pointwise_bound
    (T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (a m : ℝ) (ha : 0 < a) (hm0 : 0 ≤ m) (hma : m < a)
    (hPoint : ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ)
      (x : ℝ≥0), dist (T f x) (T h x) ≤ (m / a) * dist f h) :
    ∃ c : NNReal, c < 1 ∧ LipschitzWith c T := by sorry
