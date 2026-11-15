-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb80c_finite_measure_bounded_antitone_integral_converges
-- name    : AvramDividend.Classical.avram_bvb80c_finite_measure_bounded_antitone_integral_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:17:56.918224+00:00
-- url     : https://prove2.me/theorems/145218b1-4fd9-4f37-8035-fa6c48e2b2f8
-- title:
--   Uniformly bounded measurable antitone kernels on a finite measure have convergent real integrals
-- statement:
--   For an arbitrary finite measure, a sequence of jointly real-valued measurable integrands, uniformly bounded in absolute value and decreasing pointwise, has convergent real Bochner integral values. This cleanly isolates the analytic convergence step for original finite-activity marked jump integrals Jn, without making assumptions on martingale expectations or postpayment values.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb80c_finite_measure_bounded_antitone_integral_converges
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hMeas : ∀ n, Measurable (f n))
    (hBound : ∀ n a, ‖f n a‖ ≤ K)
    (hAnti : ∀ n m, n ≤ m → ∀ a, f m a ≤ f n a) :
    ∃ v : ℝ, Tendsto (fun n : ℕ => ∫ a, f n a ∂μ)
      atTop (𝓝 v) := by sorry
