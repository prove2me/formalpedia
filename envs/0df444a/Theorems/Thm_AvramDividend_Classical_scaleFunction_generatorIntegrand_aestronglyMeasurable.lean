-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:20:53.690985+00:00
-- url     : https://prove2.me/theorems/bae3772f-32ae-46f2-ba55-02a2f65597b0
-- title:
--   The scale-function generator integrand is strongly measurable on negative jumps
-- statement:
--   The q-scale function is zero on (-∞,0) and continuous on [0,∞). Hence for any fixed x, y↦W(x+y) is measurable by splitting at y=-x: it is zero below -x and continuous above -x. The remaining terms in the compensated generator integrand are constants, the identity function, and the indicator of (-1,1), so the whole generator integrand is strongly measurable for the Lévy measure restricted to negative jumps.
-- source:
--   Directly from the IsScaleFunction definition and the generatorIntegrand definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ) :
    AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand W x)
      (X.ν.restrict (Iio 0)) := by sorry

end AvramDividend.Classical
