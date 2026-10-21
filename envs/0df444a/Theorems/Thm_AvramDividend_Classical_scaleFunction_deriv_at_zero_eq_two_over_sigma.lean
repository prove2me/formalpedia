-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_at_zero_eq_two_over_sigma
-- name    : AvramDividend.Classical.scaleFunction_deriv_at_zero_eq_two_over_sigma
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T05:34:54.990849+00:00
-- url     : https://prove2.me/theorems/ff2f6450-2c1c-4b28-a4bc-71240c029e38
-- title:
--   The right slope of the q-scale function at the origin is two over the Gaussian coefficient
-- statement:
--   Let `X` be a spectrally negative Lévy process with a strictly positive Gaussian coefficient `σ`, let `q > 0` and let `W` be its `q`-scale function. Suppose the scale function vanishes at the origin, is differentiable at every point of the positive half-line, and is right-continuous at the origin. Then the derivative of the scale function at the origin is `2 / σ²`, the reciprocal of the Gaussian variance rate. This is the *origin normalisation* of the scale function: it is the hypothesis that the weighted Laplace transform of the generator residual needs in order to vanish, because the discounted Gaussian-and-drift part of the residual picks up the term `-(σ²/2) · W'(0) = -1`. Together with `W 0 = 0` it makes the discounted transform of the residual identically zero, which is the analytic core of the q-harmonicity `Γ W = q W` of the scale function.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the origin normalisation of the q-scale function, obtained by letting the Laplace parameter tend to zero in the scale-function identity `int_0^inf e^{-theta y} W(y) dy = (psi(theta) - q)^{-1}` and comparing the two sides of the resulting Abelian comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_deriv_at_zero_eq_two_over_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hzero : W 0 = 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0) :
    deriv W 0 = 2 / X.σ ^ 2 := by sorry

end AvramDividend.Classical
