-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_quadratic_bound_of_contDiffOn_two
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_bound_of_contDiffOn_two
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:19:03.930988+00:00
-- url     : https://prove2.me/theorems/63e8d243-06e7-44e0-882b-5a57c3c232c9
-- title:
--   C2 scale functions have a quadratic compensated-jump bound
-- statement:
--   Fix x∈(0,a). If W is a q-scale function and C² on (0,a), then its compensated generator integrand y↦W(x+y)-W(x)-W'(x)y1_{|y|<1} is strongly measurable for the negative-jump measure and is bounded in absolute value by C·min(1,y²) for some finite C≥0. For small y this is Taylor's theorem on a compact neighbourhood of x. For negative jumps bounded away from 0, W(x+y) lies between 0 and W(x) (or is zero once x+y<0), the compensation term is bounded, and min(1,y²) has a positive lower bound.
-- source:
--   Standard local Taylor estimate plus the support and monotonicity clauses of IsScaleFunction; analytic input to Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_quadratic_bound_of_contDiffOn_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand W x)
        (X.ν.restrict (Iio 0)) ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
