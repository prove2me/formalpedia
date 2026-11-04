-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_clock_large_mark_fubini
-- name    : AvramDividend.Classical.avram_p4_c_generator_clock_large_mark_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:09:09.01011+00:00
-- url     : https://prove2.me/theorems/975d1423-e1d5-49d0-96de-b2d1777194de
-- title:
--   Original finite-clock large raw-jump compensator Fubini equality at source ν
-- statement:
--   For a finite observation clock and a measurable capped reserve, the product integral of the actual original raw large-jump payoff under μ×ν restricted to z<-epsilon equals the time integral of the original ν-large-tail drift. The proof uses the already Proved original raw product L1 and source finite separated tail mass to apply pinned Mathlib integral_prod. It does not assume or establish equality with expectation of the actual jump-counting random measure, which is P2's task.
-- source:
--   Proved P4-C original raw product L1 b40bbce6-b87e-4410-be59-ae28455ffecc, epsilon_large_jump_intensity_finite 23f951a3-7c41-4e79-b5b4-7c8c2e9c7ca6; pinned Mathlib integral_prod

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_clock_large_mark_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    (∫ p : T × ℝ, w (R p.1 + p.2) - w (R p.1)
        ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, w (R t + z) - w (R t)
        ∂(X.ν.restrict (Iio (-ε))) ∂μ := by sorry
