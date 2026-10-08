-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
-- name    : AvramDividend.Classical.scaleFunction_shiftedLaplace_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:34:56.958445+00:00
-- url     : https://prove2.me/theorems/da4289b8-4c69-4413-9dc5-db822dccb613
-- title:
--   Integrability of the exponentially weighted negative shift of a q-scale function
-- statement:
--   Let W be a q-scale function. For theta>=0 with psi(theta)>q, its exponentially weighted positive-half-line restriction is integrable by the definition. For every nonpositive shift y, W is globally nonnegative and nondecreasing, hence 0<=W(x+y)<=W(x) for x>0. The shifted weighted integrand is measurable and dominated by the original weighted integrand, making it integrable on (0,infinity). This is the independent integrability prerequisite for passing from fixed-jump Laplace transforms to a Levy jump-integral transform.
-- source:
--   Direct domination from IsScaleFunction support, monotonicity and weighted integrability. Analytic prerequisite to the generator calculation in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_shiftedLaplace_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + y))
      (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
