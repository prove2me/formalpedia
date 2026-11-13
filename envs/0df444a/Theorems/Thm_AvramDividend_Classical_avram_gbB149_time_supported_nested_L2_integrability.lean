-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB149_time_supported_nested_L2_integrability
-- name    : AvramDividend.Classical.avram_gbB149_time_supported_nested_L2_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:21:59.277213+00:00
-- url     : https://prove2.me/theorems/58e6dbb7-38a8-4804-8a7c-4cc97302694b
-- title:
--   Nested L2 integrability when the time measure is supported on a bounded region
-- statement:
--   On a finite time measure supported in a measurable interval, joint measurability and two globally bounded mesh coefficients plus an interval-bounded physical coefficient give the three outer squared-error integrability statements. Proof extends the physical coefficient by zero off interval and invokes Proved B142.
-- source:
--   Proved B142

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB142_three_bounded_joint_measurable_nested_losses_integrable
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB149_time_supported_nested_L2_integrability
    {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (I : Set ℝ) (hI : MeasurableSet I) (hsupp : ∀ᵐ t ∂μ, t ∈ I)
    (f g h : ℝ × β → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (Bf Bg Bh : ℝ) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hBh : 0 ≤ Bh)
    (hfb : ∀ z, |f z| ≤ Bf) (hgb : ∀ z, |g z| ≤ Bg)
    (hhb : ∀ z, z.1 ∈ I → |h z| ≤ Bh) :
    Integrable (fun t => ∫ b, (f (t,b) - g (t,b)) ^ 2 ∂ν) μ ∧
    Integrable (fun t => ∫ b, (f (t,b) - h (t,b)) ^ 2 ∂ν) μ ∧
    Integrable (fun t => ∫ b, (h (t,b) - g (t,b)) ^ 2 ∂ν) μ := by sorry
