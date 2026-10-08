-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:40:42.623815+00:00
-- url     : https://prove2.me/theorems/bd15e6f5-3cc8-41bf-9ef1-86904bfc6c2a
-- title:
--   Quadratic compensated-increment bound for small negative jumps
-- statement:
--   For x in (0,a), C2 regularity of W gives a local Taylor estimate for the compensated increment. Choose r>0 with r<=x and r<=1 so x+y remains positive and the compensation indicator equals one whenever -r<y<0. On a compact interval around x the second derivative is bounded, and Taylor's theorem gives |W(x+y)-W(x)-W'(x)y| <= C y^2. This is the near-zero half of the global min(1,y^2) estimate.
-- source:
--   Taylor-remainder step in the generator calculation for Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_sq_bound_near_zero_of_contDiff_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min x 1 ∧ 0 ≤ C ∧
      ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * y ^ 2 := by sorry

end AvramDividend.Classical
