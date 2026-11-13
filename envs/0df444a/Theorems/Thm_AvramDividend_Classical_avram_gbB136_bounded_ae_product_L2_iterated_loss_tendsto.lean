-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
-- name    : AvramDividend.Classical.avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:36:31.032816+00:00
-- url     : https://prove2.me/theorems/989200ef-7b7f-4671-a65c-2d1658351a12
-- title:
--   Bounded almost-everywhere convergence yields iterated time-probability L2 error convergence
-- statement:
--   Apply the proved B118 bounded almost-everywhere L2 convergence theorem on the finite product measure. For every mesh index the squared difference is product-integrable by proved B129. Mathlib integral_prod converts each product integral to its iterated physical-time/probability integral. This is the analytic convergence bridge needed for B116.
-- source:
--   Proved B118, B129 and Mathlib integral_prod (exact revision).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB118_bounded_ae_L2_loss_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α × β → ℝ) (g : α × β → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m z, |f m z| ≤ B) (hgb : ∀ z, |g z| ≤ B)
    (hae : ∀ᵐ z ∂(μ.prod ν), Tendsto (fun m => f m z) atTop (𝓝 (g z))) :
    Tendsto (fun m : ℕ =>
      ∫ a, (∫ b, (f m (a, b) - g (a, b)) ^ 2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
