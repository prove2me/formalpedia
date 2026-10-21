-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
-- name    : AvramDividend.Classical.scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T05:43:54.487987+00:00
-- url     : https://prove2.me/theorems/62495c30-344f-4493-8c5c-065915fe8ac3
-- title:
--   The right slope of the q-scale function at the origin is two over the Gaussian coefficient
-- statement:
--   Let `X` be a spectrally negative Lévy process with a strictly positive Gaussian coefficient `σ`, let `q > 0` and let `W` be its `q`-scale function. Suppose the scale function vanishes at the origin and is differentiable at every point of the positive half-line. Then the derivative of the scale function tends to `2 / σ²` as the point tends to the origin from the right. This is the *origin normalisation* of the scale function: it is the hypothesis that the weighted Laplace transform of the generator residual needs in order to vanish, because the discounted Gaussian-and-drift part of the residual picks up the term `-(σ²/2) · η` where `η` is the right slope of the scale function at the origin, and the normalisation is exactly `(σ²/2) · η = 1`. Together with `W 0 = 0` it makes the discounted transform of the residual identically zero, which is the analytic core of the q-harmonicity `Γ W = q W` of the scale function. Note that the statement is a *right-limit* one: the scale function vanishes on the negative half-line, so its left derivative at the origin is `0` whenever `W 0 = 0`.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the origin normalisation of the q-scale function, obtained from the scale-function identity `int_0^inf e^{-theta y} W(y) dy = (psi(theta) - q)^{-1}` by letting the Laplace parameter tend to zero and comparing the two sides.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hzero : W 0 = 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by sorry

end AvramDividend.Classical
