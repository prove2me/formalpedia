-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_paired_dominated_integral_difference_zero
-- name    : AvramDividend.Classical.avram_bva20_paired_dominated_integral_difference_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:24:50.091237+00:00
-- url     : https://prove2.me/theorems/ca1a8182-531d-4610-955f-26f07276880e
-- title:
--   Paired bounded dominated-convergence integral sequences have vanishing difference
-- statement:
--   If two actual real-valued integrand sequences over the same finite measure are a.e. measurable, uniformly norm bounded and converge almost everywhere to the same limiting function, then their real integrals have difference tending to zero. This exact paired-DCT assembly is the final functional-analytic bridge for proving the original compensated-K minus inclusive-grid-A limit 7ccc2a1a, after representing both by the same finite time measure.
-- source:
--   Original stopped-compensator 7ccc2a1a proof gateway: paired dominated convergence for K and A over finite physical horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bva20_paired_dominated_integral_difference_zero
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure μ] (B : ℝ)
    (F G : ℕ → α → ℝ) (f : α → ℝ)
    (hFmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) μ)
    (hGmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (G n) μ)
    (hFbound : ∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ B)
    (hGbound : ∀ n, ∀ᵐ t ∂μ, ‖G n t‖ ≤ B)
    (hFlim : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n : ℕ => F n t) Filter.atTop (nhds (f t)))
    (hGlim : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n : ℕ => G n t) Filter.atTop (nhds (f t))) :
    Filter.Tendsto
      (fun n : ℕ => (∫ t, F n t ∂μ) - (∫ t, G n t ∂μ))
      Filter.atTop (nhds (0 : ℝ)) := by sorry
