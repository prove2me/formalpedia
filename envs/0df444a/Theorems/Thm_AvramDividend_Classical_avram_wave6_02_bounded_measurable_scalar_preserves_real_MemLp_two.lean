-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_bounded_measurable_scalar_preserves_real_MemLp_two
-- name    : AvramDividend.Classical.avram_wave6_02_bounded_measurable_scalar_preserves_real_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:34:48.305292+00:00
-- url     : https://prove2.me/theorems/be573fcb-6d89-4a4e-8912-6dc0c21a02c3
-- title:
--   Bounded measurable predictable scalar preserves real L²(P) MemLp integrability
-- statement:
--   A measurable scalar multiplier bounded by one preserves membership of a real-valued measurable kernel in MemLp 2 on any measure space. The controlled Lévy application uses the source-specific stopped time discount weight a(t,ω)=1_{t≤T}exp(-qt), so no additional jump-moment assumption is needed to pass from actual stopped Taylor L² to discounted L².
-- source:
--   Pinned Mathlib MeasureTheory.MemLp.mono and Real.norm_eq_abs; signature remotely verified at exact Mathlib revision.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave6_02_bounded_measurable_scalar_preserves_real_MemLp_two
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f a : α → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfm : Measurable f) (ham : Measurable a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
    MemLp (fun p => a p * f p) (2 : ℝ≥0∞) μ := by sorry
