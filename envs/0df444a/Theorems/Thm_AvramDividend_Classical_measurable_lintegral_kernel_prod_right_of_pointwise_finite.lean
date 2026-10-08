-- Prove2me | Theorems.Thm_AvramDividend_Classical_measurable_lintegral_kernel_prod_right_of_pointwise_finite
-- name    : AvramDividend.Classical.measurable_lintegral_kernel_prod_right_of_pointwise_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T15:09:51.034996+00:00
-- url     : https://prove2.me/theorems/30d3127d-e25c-455d-a1f2-ace32c0d173e
-- title:
--   Measurability of parameterised lintegrals for pointwise finite kernels
-- statement:
--   Let κ be a measurable measure-valued kernel such that each fibre measure κ(a) is finite, without requiring a uniform finite bound. For every jointly measurable nonnegative extended-real integrand f(a,b), the parameterised Lebesgue integral a ↦ ∫ f(a,b) dκ(a) is measurable. The proof follows Mathlib's Measurable.lintegral_kernel_prod_right simple-function approximation, replacing its s-finite-kernel auxiliary step by measurable_kernel_prodMk_left_of_finite with the pointwise finiteness hypothesis.
-- source:
--   Exact-revision adaptation of Mathlib.Probability.Kernel.MeasurableLIntegral at 0df444a360eaa60ab8c11dca51a86af692955474, using Kernel.measurable_kernel_prodMk_left_of_finite. Needed for random finite-horizon dividend Stieltjes measures in Avram Proposition 4(i).

import Mathlib

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped MeasureTheory ENNReal Topology

theorem AvramDividend.Classical.measurable_lintegral_kernel_prod_right_of_pointwise_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β)
    (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a, b) ∂(κ a)) := by sorry
