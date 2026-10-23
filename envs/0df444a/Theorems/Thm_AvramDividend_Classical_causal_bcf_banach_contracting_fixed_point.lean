-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_bcf_banach_contracting_fixed_point
-- name    : AvramDividend.Classical.causal_bcf_banach_contracting_fixed_point
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:12:31.17299+00:00
-- url     : https://prove2.me/theorems/ed812a82-2673-471e-adce-0be56b46d119
-- title:
--   Banach fixed point on bounded continuous functions over nonnegative time
-- statement:
--   Every strict contraction on the complete sup-norm space BoundedContinuousFunction ℝ≥0 ℝ has a fixed point. This isolates the exact pinned Mathlib metric-space instance and Banach fixed-point interface for the weighted causal Volterra resolvent construction; the integral operator itself is a separate analytic lemma.
-- source:
--   Pinned Mathlib ContractingWith.exists_fixedPoint and edist_ne_top, on BoundedContinuousFunction ℝ≥0 ℝ.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_bcf_banach_contracting_fixed_point
    (F : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (c : ℝ≥0) (hc : c < 1)
    (hF : ContractingWith c F) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ, F f = f := by sorry
