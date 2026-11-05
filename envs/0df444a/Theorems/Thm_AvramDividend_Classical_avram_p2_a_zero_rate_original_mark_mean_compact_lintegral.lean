-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mark_mean_compact_lintegral
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_compact_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:19:07.545191+00:00
-- url     : https://prove2.me/theorems/48ad4941-46ac-4883-b9f9-1b12e104d423
-- title:
--   Original marked jump mean measure agrees with original Lévy ν on compact-negative nonnegative tests
-- statement:
--   For the original sample-space Lévy jump counting measure, construct its exact finite-horizon expected mark measure and prove equality of each nonnegative compact-negative continuous test lintegral with the original T-weighted Lévy measure. Obtain the pathwise finite marked sum from the P2-A original count-to-sum lemma, its expected ENNReal value from the original jump-sum source moment, and transport via the original mark kernel Tonelli identity. No boundary indicator convergence or compensator premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_compact_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        markRate B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, ENNReal.ofReal (g y) ∂markRate) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
