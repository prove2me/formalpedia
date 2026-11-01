-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
-- name    : AvramDividend.Classical.avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:02:53.770009+00:00
-- url     : https://prove2.me/theorems/c4ffdccf-0298-40b3-a72a-d3f1f953ed8d
-- title:
--   AvramDividend.Classical.avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound from oversized parent candidate 01018f56b3a275584c162900c495e0b02b7537c55f801151fbe48b3a003e6e5c.
-- source:
--   candidate-decomposition:fbf83acf-1bfd-45ee-8c96-930992cc1901:01018f56b3a275584c162900c495e0b02b7537c55f801151fbe48b3a003e6e5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hzero : ∀ z : ℝ, z < 0 → f z = 0)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by sorry
end AvramDividend.Classical
