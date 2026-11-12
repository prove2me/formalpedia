-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb66_filtered_predictable_multiplier_condExp_zero
-- name    : AvramDividend.Classical.avram_gb66_filtered_predictable_multiplier_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:18:43.371439+00:00
-- url     : https://prove2.me/theorems/9c5e3e5b-30c6-4b08-9239-97bd0835cab3
-- title:
--   A filtered measurable integrable multiplier preserves zero conditional expectation
-- statement:
--   For a real random variable Q with conditional mean zero given a sub-sigma-algebra and an integrable weighted product H Q, any multiplier H strongly measurable in that sub-sigma-algebra can be pulled out of conditional expectation, giving conditional mean zero for H Q. This is the standard conditional expectation pull-out property needed for original stopped Gaussian quadratic increments.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_gb66_filtered_predictable_multiplier_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓢 : MeasurableSpace Ω) (H Q : Ω → ℝ)
    (hH : StronglyMeasurable[𝓢] H)
    (hHQ : Integrable (fun ω => H ω * Q ω) P)
    (hQ : Integrable Q P)
    (hQzero : P[Q | 𝓢] =ᵐ[P] (fun _ => 0)) :
    P[(fun ω => H ω * Q ω) | 𝓢] =ᵐ[P] (fun _ => 0) := by sorry
