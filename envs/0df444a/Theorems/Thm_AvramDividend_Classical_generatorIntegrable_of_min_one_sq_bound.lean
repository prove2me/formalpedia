-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_one_sq_bound
-- name    : AvramDividend.Classical.generatorIntegrable_of_min_one_sq_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:15:59.977343+00:00
-- url     : https://prove2.me/theorems/edc86303-e839-4403-bafe-f48d744cc4dd
-- title:
--   Quadratic Lévy bound implies generator jump-integrability
-- statement:
--   A reusable measure-theoretic lemma for this mission. The Lévy structure assumes ∫ min(1,y²) ν(dy)<∞. Therefore, if the compensated generator integrand is strongly measurable on the negative-jump region and its absolute value is bounded there by C·min(1,y²) for some C≥0, then it is integrable on (-∞,0), i.e. GeneratorIntegrable holds. This isolates the domination argument from the calculus needed to produce the quadratic bound.
-- source:
--   Direct consequence of the Lévy-measure integrability condition in Def_AvramDividend_Classical_SpectrallyNegativeLevy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrable_of_min_one_sq_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x C : ℝ)
    (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ y ∈ Iio (0 : ℝ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤
        C * min 1 (y ^ 2)) :
    X.GeneratorIntegrable f x := by sorry

end AvramDividend.Classical
