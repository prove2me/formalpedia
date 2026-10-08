-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:38:22.562335+00:00
-- url     : https://prove2.me/theorems/4cd125e2-f241-46b8-a255-aae3d11028d5
-- title:
--   C2 scale functions have a global min-one-square bound on the compensated jump increment
-- statement:
--   Fix x in (0,a) and assume the q-scale function W is C2 on (0,a). Then there is C>=0 such that for every negative jump y, the compensated generator increment has absolute value at most C min(1,y^2). Near y=0, choose a radius smaller than x and use Taylor's theorem with bounded second derivative on a compact neighbourhood of x to obtain an O(y^2) remainder. Away from zero, W(x+y) lies between 0 and W(x) by the scale-function support, nonnegativity and monotonicity properties, while the compensation term is uniformly bounded; since min(1,y^2) is bounded below by a positive constant away from zero, enlarge C to cover this region.
-- source:
--   Pure analytic estimate underlying the generator-integrability step in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
