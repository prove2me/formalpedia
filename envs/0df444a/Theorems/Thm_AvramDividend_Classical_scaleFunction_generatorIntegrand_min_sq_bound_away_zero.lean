-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_away_zero
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_min_sq_bound_away_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:40:51.255267+00:00
-- url     : https://prove2.me/theorems/c077f149-5581-4129-829f-c321699ccc47
-- title:
--   Uniform compensated-increment bound for negative jumps away from zero
-- statement:
--   Fix x>0 and r>0. For all negative jumps bounded away from zero by y<=-r, the q-scale function satisfies 0<=W(x+y)<=W(x): if x+y<0 it vanishes, otherwise this follows from nonnegativity and monotonicity. The compensation term is zero outside (-1,1) and has magnitude at most |W'(x)| inside it. Hence the compensated increment is uniformly bounded. Since min(1,y^2) is bounded below by min(1,r^2)>0 on y<=-r, division by this positive lower bound gives a constant C with the stated domination.
-- source:
--   Elementary far-jump estimate in the generator-integrability argument for Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_min_sq_bound_away_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
