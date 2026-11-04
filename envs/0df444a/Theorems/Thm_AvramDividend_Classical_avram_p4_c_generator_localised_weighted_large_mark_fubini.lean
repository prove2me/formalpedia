-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_large_mark_fubini
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_weighted_large_mark_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:34:29.280766+00:00
-- url     : https://prove2.me/theorems/92a1ea9a-1470-493a-96b8-c99c4899a009
-- title:
--   Fubini for original discounted negative large jumps on measurable stopped region with local reserve cap
-- statement:
--   The actual spectrally-negative Levy source νtail raw-jump payoff, discounted by bounded measurable time weight a and masked to measurable stopped clock region A, has a Fubini identity from μ times original νtail to iterated νtail then μ. The reserve cap is only assumed on A; the source-specific masked bounded-weight product L1 theorem is already Proved.
-- source:
--   Accepted P4-C avram_p4_c_generator_localised_weighted_raw_large_mark_L1 (91881f55-3e9b-48fd-9566-bf1a2ef95f40), epsilon_large_jump_intensity_finite; pinned Mathlib integral_prod.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_weighted_large_mark_fubini
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
    (∫ p : T × ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => a s.1 * (w (R s.1 + s.2) - w (R s.1)))) p
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => a s.1 * (w (R s.1 + s.2) - w (R s.1)))) (t,z)
      ∂(X.ν.restrict (Iio (-ε))) ∂μ := by sorry
