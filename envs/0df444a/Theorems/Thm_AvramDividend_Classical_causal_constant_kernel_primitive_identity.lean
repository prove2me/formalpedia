-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_constant_kernel_primitive_identity
-- name    : AvramDividend.Classical.causal_constant_kernel_primitive_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:06:56.055802+00:00
-- url     : https://prove2.me/theorems/8c9de199-74d1-4cc5-91d7-94dc68159ee6
-- title:
--   Constant-kernel causal convolution commutes with taking a primitive
-- statement:
--   For any real function g, scalar β, and endpoint x, the constant-kernel contribution β times the causal integral of g can be pulled through its inner integral. The resulting outer integrands are identical up to bound-variable renaming. This isolates the elementary part of the full L1-plus-constant Volterra Fubini identity.
-- source:
--   Linearity of the Bochner set integral, specifically integral_const_mul.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_constant_kernel_primitive_identity
    (g : ℝ → ℝ) (β x : ℝ) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      β * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by sorry
