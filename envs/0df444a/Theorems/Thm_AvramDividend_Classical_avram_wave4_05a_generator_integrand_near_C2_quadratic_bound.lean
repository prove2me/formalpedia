-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_generator_integrand_near_C2_quadratic_bound
-- name    : AvramDividend.Classical.avram_wave4_05a_generator_integrand_near_C2_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:02:50.547232+00:00
-- url     : https://prove2.me/theorems/4bf1ae78-cbbd-4942-bb55-9fb0b50be1d0
-- title:
--   AvramDividend.Classical.avram_wave4_05a_generator_integrand_near_C2_quadratic_bound
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_wave4_05a_generator_integrand_near_C2_quadratic_bound from oversized parent candidate 01018f56b3a275584c162900c495e0b02b7537c55f801151fbe48b3a003e6e5c.
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
theorem avram_wave4_05a_generator_integrand_near_C2_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min x 1 ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * y ^ 2 := by sorry
end AvramDividend.Classical
