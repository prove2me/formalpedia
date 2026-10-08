-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_one_abs_bound_boundedVariation
-- name    : AvramDividend.Classical.generatorIntegrable_of_min_one_abs_bound_boundedVariation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:36:00.973785+00:00
-- url     : https://prove2.me/theorems/69c9f15a-79bb-4420-bd7d-1acc33fcdfee
-- title:
--   Linear Lévy bound implies generator integrability in bounded variation
-- statement:
--   A reusable bounded-variation domination lemma. The preceding weight theorem makes min(1,|y|) integrable on negative jumps. Therefore any strongly measurable compensated generator integrand bounded in absolute value by C·min(1,|y|), with C≥0, is generator-integrable by scalar multiplication and Integrable.mono'.
-- source:
--   Direct measure-theoretic consequence of boundedVariation_min_one_abs_integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrable_of_min_one_abs_bound_boundedVariation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (f : ℝ → ℝ) (x C : ℝ)
    (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ y ∈ Iio (0 : ℝ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤
        C * min 1 |y|) :
    X.GeneratorIntegrable f x := by sorry

end AvramDividend.Classical
