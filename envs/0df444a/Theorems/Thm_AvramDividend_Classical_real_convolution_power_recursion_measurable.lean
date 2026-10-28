-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_convolution_power_recursion_measurable
-- name    : AvramDividend.Classical.real_convolution_power_recursion_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:40:36.528989+00:00
-- url     : https://prove2.me/theorems/4d6ed155-00a4-465d-8f47-6492ce4d9d8b
-- title:
--   Measurability of every real convolution power from its exact recursive integral
-- statement:
--   For any measurable real kernel k and any exact sequence of pointwise real convolution powers, prove every F_n is measurable by induction and strong measurability of the parameterised Bochner integral. This closes a missing premise of the generic geometric-renewal density identification in the bounded-variation Esscher zero-barrier workstream.
-- source:
--   Pinned Mathlib MeasureTheory.StronglyMeasurable.integral_prod_right' and measurable product operations.

import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

theorem AvramDividend.Classical.real_convolution_power_recursion_measurable
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hk : Measurable k)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Measurable (F n)  := by sorry
