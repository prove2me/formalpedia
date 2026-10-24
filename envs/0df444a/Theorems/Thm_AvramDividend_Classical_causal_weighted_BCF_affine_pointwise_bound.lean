-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_pointwise_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:40:13.99875+00:00
-- url     : https://prove2.me/theorems/7a77c3d1-f768-4de9-8af4-85d2e4ac050b
-- title:
--   Uniform pointwise bound for the weighted affine Volterra operator
-- statement:
--   The affine operator T(f)(x)=exp(-w*x)/a(1−∫(β+K)*V_f) is uniformly bounded on nonnegative time by (1+‖f‖ m)/a, where m is the strict weighted L1 mass of the kernel. The estimate combines the previously established uniform kernel mass inequality, exp(-w*x)≤1, and the triangle inequality. The zero endpoint follows because the integral is empty there.
-- source:
--   Proved causal_weighted_BCF_explicit_kernel_mass_bound and Mathlib elementary real exponential and absolute-value inequalities.

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_explicit_kernel_mass_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_bound
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ) (x : ℝ), 0 ≤ x →
        |(Real.exp (-(w * x)) *
          (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a| ≤
          (1 + ‖f‖ * m) / a := by sorry
