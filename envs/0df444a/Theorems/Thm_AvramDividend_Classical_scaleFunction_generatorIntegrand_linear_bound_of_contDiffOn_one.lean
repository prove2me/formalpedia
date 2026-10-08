-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_linear_bound_of_contDiffOn_one
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_linear_bound_of_contDiffOn_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:39:17.026994+00:00
-- url     : https://prove2.me/theorems/e0eaf867-4320-4b36-9e4e-aa0bceae4095
-- title:
--   C1 scale functions have a global min-one-abs compensated-jump bound
-- statement:
--   Combine the local C¹ linear remainder estimate with the far-jump scale-function bound. On -r<y<0 with r<1, min(1,|y|)=|y|. For y≤-r, the existing far-jump estimate by C·min(1,y²) also implies a bound by C·min(1,|y|), because min(1,y²)≤min(1,|y|). Taking the maximum of the near and far constants yields a global negative-jump bound.
-- source:
--   Combination of the near C¹ mean-value bound and the far-jump order bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_linear_bound_of_contDiffOn_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 |y| := by sorry

end AvramDividend.Classical
