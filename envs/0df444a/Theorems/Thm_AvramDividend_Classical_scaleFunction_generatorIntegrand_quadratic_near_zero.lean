-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_quadratic_near_zero
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_near_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T13:49:53.145132+00:00
-- url     : https://prove2.me/theorems/b3185117-efca-4c66-a82a-be8e04a332c5
-- title:
--   Quadratic near-zero bound for the C2 scale-function generator integrand
-- statement:
--   If the scale function is C2 on an open interval (0,a) containing x, then its compensated generator increment is O(y^2) as the negative jump y approaches zero. More precisely there are r in (0,min(1,x)) and C>=0 such that for -r<y<0, |W(x+y)-W(x)-W'(x)y|<=C y^2; on this range the generator compensation indicator equals one. A source-faithful proof applies Mathlib's Taylor remainder bound to the reflected function g(t)=W(x-t) on [0,r].
-- source:
--   Taylor remainder estimate applied to the generator formula in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_generatorIntegrand_quadratic_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ r C : ℝ,
      0 < r ∧ r ≤ 1 ∧ r < x ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * y ^ 2 := by sorry
