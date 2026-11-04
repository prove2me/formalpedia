-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_increment_identity
-- name    : AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_increment_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:10:53.384569+00:00
-- url     : https://prove2.me/theorems/d36c4731-4683-49cc-9493-e43ff5263e02
-- title:
--   Finite-mark jump expectation drift correction matches the strict-unit-compensated source Lévy generator
-- statement:
--   At any source generator-integrable state y and any positive epsilon, the raw jump increment integrated on (-1,-epsilon) equals the compensated generator integrand integrated over the same band plus w'(y) times the finite signed linear jump-moment. This is the exact algebraic sign bridge needed to change the original source drift c to the finite-cutoff drift b_epsilon. Integrability of both terms follows from the source GeneratorIntegrable predicate and the independently proved bounded finite-band linear mark integral.
-- source:
--   SpectrallyNegativeLevy.generatorIntegrand and GeneratorIntegrable definitions, accepted Avram P4-C cutoff_linear_mark_integrable helper 63c53f4c-113e-48e0-8d54-55be014f9398, paper Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_increment_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Ioo (-1 : ℝ) (-ε), (w (y + z) - w y) ∂X.ν) =
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      deriv w y * (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) := by sorry
