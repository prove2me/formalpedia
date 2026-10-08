-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_near_quadratic_bound
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_near_quadratic_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:25:53.468985+00:00
-- url     : https://prove2.me/theorems/f76a6206-f3a1-453e-81cb-69b8cafadfa4
-- title:
--   Local quadratic bound for the compensated scale-function jump remainder
-- statement:
--   Local Taylor estimate. For x in an interval where the q-scale function W is C², choose 0<r<min(1,x) with [x-r,x] contained in (0,a). Since |y|<1 for y∈(-r,0), the compensation indicator equals 1. Taylor's theorem around x, with the second derivative bounded on the compact interval [x-r,x], gives |W(x+y)-W(x)-W'(x)y|≤C y² uniformly on that range.
-- source:
--   Mathlib Taylor remainder theorem applied to the C² scale function; analytic estimate underlying Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_near_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < x ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ C * y ^ 2 := by sorry

end AvramDividend.Classical
