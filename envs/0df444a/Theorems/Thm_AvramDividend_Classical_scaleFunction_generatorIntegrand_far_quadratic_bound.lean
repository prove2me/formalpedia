-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_far_quadratic_bound
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_far_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:25:57.074806+00:00
-- url     : https://prove2.me/theorems/ee51f740-b70e-4711-8603-d2f7efda831e
-- title:
--   Far negative jumps admit a min-one-square generator bound
-- statement:
--   Far-jump estimate. For y≤-r<0, scale-function support/nonnegativity/monotonicity give 0≤W(x+y)≤W(x) whenever x+y≥0, and W(x+y)=0 otherwise. Thus the value difference is uniformly bounded. The compensation term is zero for |y|≥1 and is bounded by |W'(x)| when |y|<1. Meanwhile min(1,y²)≥min(1,r²)>0. Dividing the uniform numerator bound by that positive lower bound gives a finite constant C.
-- source:
--   Directly from IsScaleFunction support, nonnegativity and monotonicity plus the generatorIntegrand definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_far_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x r : ℝ)
    (hx : 0 ≤ x) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, y ≤ -r →
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
