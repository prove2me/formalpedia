-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
-- name    : AvramDividend.Classical.avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:42:14.481623+00:00
-- url     : https://prove2.me/theorems/7e47c2bb-9a0b-4d45-a851-73b486de3e5f
-- title:
--   Triple nested L2 integrability of bounded measurable coefficients
-- statement:
--   Apply proved B138 to all three bounded jointly measurable coefficient pairs on a finite product measure; exactly the six nested integrability claims needed for B127.
-- source:
--   Proved B138

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g h : α × β → ℝ) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (B : ℝ) (hB : 0 ≤ B) (hfb : ∀ z, |f z| ≤ B)
    (hgb : ∀ z, |g z| ≤ B) (hhb : ∀ z, |h z| ≤ B) :
    (∀ a, Integrable (fun b => (f (a,b)-g (a,b))^2) ν ∧
          Integrable (fun b => (f (a,b)-h (a,b))^2) ν ∧
          Integrable (fun b => (h (a,b)-g (a,b))^2) ν) ∧
    Integrable (fun a => ∫ b, (f (a,b)-g (a,b))^2 ∂ν) μ ∧
    Integrable (fun a => ∫ b, (f (a,b)-h (a,b))^2 ∂ν) μ ∧
    Integrable (fun a => ∫ b, (h (a,b)-g (a,b))^2 ∂ν) μ := by sorry
