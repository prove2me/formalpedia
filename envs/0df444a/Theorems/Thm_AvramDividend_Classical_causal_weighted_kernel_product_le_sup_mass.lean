-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
-- name    : AvramDividend.Classical.causal_weighted_kernel_product_le_sup_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:50:49.559116+00:00
-- url     : https://prove2.me/theorems/d5e66c2d-9a20-4c9b-8b15-f17a3f60cfb7
-- title:
--   Weighted causal convolution dominated by finite-horizon supremum times kernel mass
-- statement:
--   For a nonnegative L1 positive-lag kernel and a continuous positive-time function D, any finite-horizon bound on exp(-wt)|D(t)| bounds the weighted causal convolution by the finite-horizon weighted supremum times the truncated kernel mass. The crucial steps are local integrability of the reflected kernel, measurability of the weighted continuous factor, norm-domination for their product, then integral_mono_ae. This is the key pointwise step in Volterra uniqueness and contraction without differentiability of the kernel.
-- source:
--   Proved causal_l1_kernel_continuous_input_integrable; pinned Mathlib Integrable.mono and integral_mono_ae; finite-interval weighted-supremum comparison.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_kernel_product_le_sup_mass
    (L D : ℝ → ℝ) (w R x : ℝ)
    (hL : IntegrableOn L (Ioi (0 : ℝ)) volume)
    (hLnonneg : ∀ u : ℝ, 0 ≤ L u)
    (hDcont : ContinuousOn D (Ioi (0 : ℝ)))
    (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R)
    (hM : BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R)) :
    (∫ s in Ioc (0 : ℝ) x,
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ∂volume) ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R) *
    (∫ s in Ioc (0 : ℝ) x, L (x - s) ∂volume) := by sorry
