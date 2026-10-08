-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_quadratic_bound_pointwise
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_bound_pointwise
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:22:24.261012+00:00
-- url     : https://prove2.me/theorems/8b70ba57-e2fe-4150-b825-61c90f18427a
-- title:
--   Pointwise quadratic bound for the C2 scale-function jump remainder
-- statement:
--   Pure calculus/order core of the C² generator-integrability argument. Fix x∈(0,a). For sufficiently small negative y, C² regularity gives a Taylor remainder bound |W(x+y)-W(x)-W'(x)y|≤M y². For y bounded away from zero, scale-function support, nonnegativity and monotonicity bound W(x+y), while the compensation term is bounded and min(1,y²) is bounded below by a positive constant. Combining the two regions yields a finite C≥0 with |generatorIntegrand W x y|≤C min(1,y²) for all y<0.
-- source:
--   Taylor's theorem plus the support/nonnegativity/monotonicity clauses of IsScaleFunction; analytic estimate underlying Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_quadratic_bound_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
