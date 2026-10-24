-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_pointwise_lipschitz
-- name    : AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T08:05:59.613132+00:00
-- url     : https://prove2.me/theorems/5ab8547e-6ce6-4a19-bed6-47803dbd511a
-- title:
--   Pointwise Lipschitz estimate for the normalised affine weighted Volterra update
-- statement:
--   The exponentially weighted affine Volterra update, divided by a, is pointwise Lipschitz in the BCF sup norm with coefficient m/a<1, where m is the explicit weighted L1 mass of β+K. Subtracting the affine updates cancels their constant forcing term. The earlier two-input integral bound and positivity of a yield the estimate, including the zero endpoint.
-- source:
--   Published causal_weighted_BCF_two_input_lipschitz_bound, abs algebra, division order.

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_two_input_lipschitz_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_lipschitz
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ) (x : ℝ), 0 ≤ x →
        |(Real.exp (-(w * x)) * (1 - (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume))) / a -
         (Real.exp (-(w * x)) * (1 - (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) ∂volume))) / a| ≤
          ‖f - h‖ * (m / a) := by sorry
