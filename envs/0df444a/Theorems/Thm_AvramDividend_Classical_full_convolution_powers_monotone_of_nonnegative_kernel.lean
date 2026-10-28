-- Prove2me | Theorems.Thm_AvramDividend_Classical_full_convolution_powers_monotone_of_nonnegative_kernel
-- name    : AvramDividend.Classical.full_convolution_powers_monotone_of_nonnegative_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:01:57.659457+00:00
-- url     : https://prove2.me/theorems/ca86ab68-4be1-4013-93bc-9d2743c08824
-- title:
--   Every positive causal convolution power inherits monotonicity of its kernel
-- statement:
--   For a nonnegative globally nondecreasing real kernel κ and any recursively defined full convolution powers F0=κ, F(n+1)=κ*F(n), the powers F_n are all nondecreasing when the pointwise convolution integrands are integrable. Proof by induction and monotonicity of Bochner integration. This exactly supplies the monotonicity of each zero-discount convolution-series term needed for positive-discount scale existence.
-- source:
--   Direct induction using Mathlib MeasureTheory.integral_mono; rooted at unbounded_positive_discount_scale_exists_from_zero.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory

theorem AvramDividend.Classical.full_convolution_powers_monotone_of_nonnegative_kernel
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκmono : Monotone κ)
    (hκpos : ∀ y : ℝ, 0 ≤ κ y)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hInt : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume) :
    ∀ n : ℕ, Monotone (F n) := by sorry
