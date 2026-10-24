-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_fixed_point_equation_transfer
-- name    : AvramDividend.Classical.causal_weighted_BCF_fixed_point_equation_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:52:46.203547+00:00
-- url     : https://prove2.me/theorems/cfc20918-808c-444a-b0e7-fd2f014edde2
-- title:
--   Transfer an affine weighted BCF fixed point into the Volterra resolvent equation
-- statement:
--   Suppose a bounded continuous function is a fixed point of the explicitly defined exponentially weighted affine causal Volterra self-map. At positive time, substitute the fixed-point identity, multiply by a exp(wx), cancel exp(wx)exp(−wx)=1 and rearrange. The original Volterra resolvent equation follows. This step uses only elementary algebra and the fixed-point identity.
-- source:
--   Mathlib real exponential identities, BoundedContinuousFunction evaluation, field and ring algebra.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_fixed_point_equation_transfer
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a)
    (T : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hT : ∀ (z : BoundedContinuousFunction ℝ≥0 ℝ)
      (x : ℝ) (hx : 0 ≤ x),
      T z ⟨x, hx⟩ =
        (Real.exp (-(w * x)) *
          (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) *
              z ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a)
    (hFixed : T f = f) :
    ∀ x : ℝ, 0 < x →
      a * (Real.exp (w * x) *
        f ⟨max x 0, le_max_right x 0⟩) + (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) *
              f ⟨max s 0, le_max_right s 0⟩) ∂volume) = 1 := by sorry
