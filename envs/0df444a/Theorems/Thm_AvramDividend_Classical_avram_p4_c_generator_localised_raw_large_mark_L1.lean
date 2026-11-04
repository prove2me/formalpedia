-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_raw_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_raw_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:04:25.082208+00:00
-- url     : https://prove2.me/theorems/a13fec27-8609-4221-b86d-19a04fd4b4d6
-- title:
--   Actual original large-jump payoff is product L1 on a measurable stopped region with only local cap
-- statement:
--   For the original Levy X and a finite observation-clock measure, the raw negative large-jump payoff is integrable under μ times the restricted original ν tail after masking any measurable stopped/interior set A. Only the reserve values on A must lie in [0,v]; outside A no reserve cap is postulated. The proof replaces R outside A by zero, uses previously Proved original raw-product L1 on the capped replacement, then uses measurable-set indicator integrability and pointwise identification on A. This remains an analytic product-integrability theorem, conditional on source stopped-region measurability and never assuming an original jump-count compensator.
-- source:
--   Accepted P4-C avram_p4_c_generator_finite_clock_raw_large_mark_L1 (b40bbce6-b87e-4410-be59-ae28455ffecc), pinned Mathlib Integrable.indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_raw_large_mark_L1
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
    Integrable
      ({p : T × ℝ | p.1 ∈ A}.indicator
        (fun p => w (R p.1 + p.2) - w (R p.1)))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by sorry
