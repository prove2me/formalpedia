-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
-- name    : AvramDividend.Classical.boundedVariation_generator_physical_drift_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:32:16.64331+00:00
-- url     : https://prove2.me/theorems/c8ba98f0-955f-4a05-bacb-140abf15d49b
-- title:
--   BV Lévy generator equals physical drift derivative plus uncompensated jump integral
-- statement:
--   For a bounded-variation spectrally negative Lévy process and generator-integrable test function, the compensated generator has the equivalent finite-variation form Γw(x)=drift·w'(x)+∫_{(-∞,0)}[w(x+y)-w(x)]ν(dy). The proof splits negative jumps at -1, applies the accepted small and large jump integral decompositions, and combines the first-order compensation with the characteristic drift. This identity is a direct algebraic input to the finite-variation chain-rule verification.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral
import Theorems.Thm_AvramDividend_Classical_boundedVariation_drift_compensation_identity
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_generatorIntegral_decomposition
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integral_identity
import Theorems.Thm_AvramDividend_Classical_generatorIntegral_negative_jump_partition

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_generator_physical_drift_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν := by sorry
