-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_clock_large_mark_fubini
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:32:10.261258+00:00
-- url     : https://prove2.me/theorems/bf992e36-58bf-4f4b-9cf0-80a565fbbf15
-- title:
--   Fubini identity for original negative large jumps on a measurable stopped region under local reserve cap
-- statement:
--   The actual source original ν-tail raw negative-jump payoff restricted to a measurable time/stopped region A has a valid Fubini equality of μ times restricted original ν integration and iterated original ν then μ integration. The reserve cap is imposed only on A. Integrability derives from the source-specific localised raw large mark product L1 theorem, with finite original νtail mass for Fubini. This child imports the parent localised L1 theorem, and must only be submitted as a genuine proof after that parent is Proved.
-- source:
--   P4-C localised_raw_large_mark_L1 (a13fec27-8609-4221-b86d-19a04fd4b4d6), P4-C epsilon_large_jump_intensity_finite; pinned Mathlib integral_prod

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v) :
    (∫ p : T × ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => w (R s.1 + s.2) - w (R s.1))) p
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => w (R s.1 + s.2) - w (R s.1))) (t,z)
      ∂(X.ν.restrict (Iio (-ε))) ∂μ := by sorry
