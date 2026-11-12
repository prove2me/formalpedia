-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb48_centered_fourth_integral_bound
-- name    : AvramDividend.Classical.avram_gb48_centered_fourth_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:57:38.569405+00:00
-- url     : https://prove2.me/theorems/810aa067-946e-40d1-99a6-1d076921747b
-- title:
--   Raw fourth moment controls the centred quadratic residual second moment
-- statement:
--   For a measurable real random variable with an integrable fourth power on a probability space, the square of the difference of its square from any constant is integrable. Its expected value is bounded by twice the fourth moment plus twice the squared constant. The exact elementary transfer applies to the intrinsic original Gaussian increment in gb41.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_gb48_centered_fourth_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hfourth : Integrable (fun ω => Z ω ^ 4) P) (a : ℝ) :
    Integrable (fun ω => (Z ω ^ 2 - a) ^ 2) P ∧
      (∫ ω, (Z ω ^ 2 - a) ^ 2 ∂P) ≤
        2 * (∫ ω, Z ω ^ 4 ∂P) + 2 * a ^ 2 := by
  sorry
