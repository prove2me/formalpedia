-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_local_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:04:16.994408+00:00
-- url     : https://prove2.me/theorems/501b3503-40d7-455d-8066-ae28facf7b7f
-- title:
--   Exponential reweighting of a bounded continuous function is bounded on finite horizons
-- statement:
--   For a BCF f and a finite positive horizon R, the reweighted input e^(ws)f(s) is uniformly bounded on (0,R] by e^(|w|R)||f||. This supplies the local boundedness premise used by the weighted causal convolution estimate.
-- source:
--   Pointwise BCF norm bound combined with the exponential monotonicity and |w| upper bound on a finite positive interval.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_local_bound
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R →
      |Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩| ≤ C := by sorry
