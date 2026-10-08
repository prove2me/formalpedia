-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_uniformBound_negative
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_uniformBound_negative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T13:43:34.981924+00:00
-- url     : https://prove2.me/theorems/663a7c3a-0f55-4c09-a312-710d81c4d753
-- title:
--   Uniform bound for the scale-function generator integrand on negative jumps
-- statement:
--   For fixed x>0, the q-scale function satisfies 0<=W(x+y)<=W(x) for every y<0: if x+y<0 it vanishes, while otherwise monotonicity on [0,infinity) applies. The compensation indicator is nonzero only for -1<y<0, where |y|<1. Therefore the absolute value of W(x+y)-W(x)-W'(x)y 1_{|y|<1} is uniformly bounded by 2 W(x)+|W'(x)| over all negative y. This is the far-jump bound used in the generator-integrability proof.
-- source:
--   Elementary consequence of the mission definition of IsScaleFunction and generatorIntegrand.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_generatorIntegrand_uniformBound_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := by sorry
