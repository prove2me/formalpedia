-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
-- name    : AvramDividend.Classical.generatorIntegrable_of_min_sq_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:24:25.788261+00:00
-- url     : https://prove2.me/theorems/37012faf-811a-4582-a399-a01a7af38a50
-- title:
--   Generator integrability from a Levy min-one-square domination
-- statement:
--   Generic measure-theoretic helper for the classical Levy generator. The Levy-measure structure stores finiteness of the lintegral of min(1,y^2). If the compensated generator integrand is strongly measurable on negative jumps and its norm is almost everywhere bounded by C min(1,y^2) for some C>=0, then it is integrable on (-infinity,0), hence GeneratorIntegrable holds. This separates the pure domination argument from the scale-function Taylor estimates.
-- source:
--   Direct consequence of the Levy measure moment condition in the mission definition of SpectrallyNegativeLevy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.generatorIntegrable_of_min_sq_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ᵐ y ∂X.ν.restrict (Iio 0),
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
        C * min 1 (y ^ 2)) :
    X.GeneratorIntegrable f x := by sorry
