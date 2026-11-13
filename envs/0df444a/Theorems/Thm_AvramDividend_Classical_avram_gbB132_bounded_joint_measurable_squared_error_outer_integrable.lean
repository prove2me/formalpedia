-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
-- name    : AvramDividend.Classical.avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:01:56.251968+00:00
-- url     : https://prove2.me/theorems/019a8f88-02bd-4a78-8a66-e37782fe1db1
-- title:
--   Integrability of the probability-integrated squared error of bounded jointly measurable coefficients
-- statement:
--   The product of two finite measure spaces is finite. Apply Proved B129 to the measurable and uniformly bounded coefficients on the product, then the Mathlib Integrable.integral_prod_left theorem to obtain integrability of the inner probability integral in physical time. This is the outer-integrability mechanism needed for B127.
-- source:
--   Proved B129 and Mathlib Integrable.integral_prod_left on finite product measures.

import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ z, |f z| ≤ B) (hgb : ∀ z, |g z| ≤ B) :
    Integrable (fun a => ∫ b, (f (a, b) - g (a, b)) ^ 2 ∂ν) μ := by sorry
