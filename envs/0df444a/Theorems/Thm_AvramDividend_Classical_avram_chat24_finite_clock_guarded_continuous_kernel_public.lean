-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_finite_clock_guarded_continuous_kernel_public
-- name    : AvramDividend.Classical.avram_chat24_finite_clock_guarded_continuous_kernel_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:11:28.228059+00:00
-- url     : https://prove2.me/theorems/39ab6769-d6af-43e4-8e58-9825963c3db6
-- title:
--   Guarded continuous compact kernel is integrable under a finite clock
-- statement:
--   A continuous compact reserve kernel with nonnegative discount is bounded and measurable after stopping a measurable reserve section. Integrate under any finite physical clock. Public prerequisite for the public actual-stopped integrability target.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_finite_clock_guarded_continuous_kernel_public
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (Y : ℝ≥0 → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b))
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0) :
    Integrable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0) μ := by sorry
