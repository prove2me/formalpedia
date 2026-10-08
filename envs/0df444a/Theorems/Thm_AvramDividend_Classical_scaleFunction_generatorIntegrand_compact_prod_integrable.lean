-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_compact_prod_integrable
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_prod_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:46:22.415201+00:00
-- url     : https://prove2.me/theorems/38611b0f-9bea-488a-9c9e-6f45485613a2
-- title:
--   Compact-localised compensated Lévy generator is integrable on the state–jump product
-- statement:
--   Let W be a q-scale function C2 on (0,a) and K=[l,u] a compact subset, 0<l<u<a. For any finite measure μ of starting states, the compensated negative-jump generator integrand cut off to K×(-∞,0) is integrable under μ⊗ν_negative. The proof combines three separately verifiable results: a uniform-in-x bound by C min(1,y²) on K; global joint measurability of the generator increment using the local derivative extended by zero; and the generic product-integrability domination theorem. The structure's Levy moment condition proves integrability of min(1,y²) under the restricted Levy measure. This is the rigorous product-measure prerequisite for applying Fubini on compact state intervals.
-- source:
--   Compact-localised Fubini step in the scale-function generator argument from Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_compact_prod_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable
      ((Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun p : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2))
      (μ.prod (X.ν.restrict (Iio 0))) := by sorry

end AvramDividend.Classical
