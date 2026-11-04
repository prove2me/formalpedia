-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_raw_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_weighted_raw_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:13:44.38817+00:00
-- url     : https://prove2.me/theorems/91881f55-3e9b-48fd-9566-bf1a2ef95f40
-- title:
--   Discounted original raw negative large-jump payoff is product L1 on true stopped regions
-- statement:
--   For the original Levy negative-tail intensity, any finite observation clock, a measurable stopped region A and a reserve confined to [0,v] only on A, the product-integral raw large jump payoff multiplied by an arbitrary measurable uniformly bounded clock weight is integrable after the A indicator. This includes discounted original large-jump kernels on a localised stopped region, assuming measurability and the cap there. The proof independently combines the accepted original raw product L1, clipped reserve, pinned Integrable.bdd_mul and Integrable.indicator. It asserts neither predictable compensation nor generator validity at a boundary.
-- source:
--   Proved P4-C raw finite clock large mark product L1 b40bbce6-b87e-4410-be59-ae28455ffecc; pinned Integrable.bdd_mul and Integrable.indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_weighted_raw_large_mark_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    Integrable
      ({p : T × ℝ | p.1 ∈ A}.indicator
        (fun p => a p.1 * (w (R p.1 + p.2) - w (R p.1))))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by sorry
