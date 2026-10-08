-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_near_linear_bound
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_near_linear_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:39:23.481982+00:00
-- url     : https://prove2.me/theorems/cefc30ad-50b6-442e-9e41-49297910a4d4
-- title:
--   Local linear bound for the compensated C1 scale-function jump integrand
-- statement:
--   For x inside an interval where W is C¹, choose 0<r<min(1,x) with [x-r,x] inside the interval and set g(t)=W(x-t). Taylor's theorem at degree zero, equivalently the mean-value bound, gives |W(x+y)-W(x)|≤M|y| for -r<y<0. On this range the compensation indicator is one, and |W'(x)y|=|W'(x)||y|, so the entire compensated generator integrand is bounded by (M+|W'(x)|)|y|.
-- source:
--   Mean-value/Taylor estimate from C¹ regularity; bounded-variation analytic input to Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_near_linear_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < x ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * |y| := by sorry

end AvramDividend.Classical
