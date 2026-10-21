-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_of_finite_small_jump_measure
-- name    : AvramDividend.Classical.scaleFunction_zero_origin_gaussian_of_finite_small_jump_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T16:03:26.801343+00:00
-- url     : https://prove2.me/theorems/16b2ff3e-9cf2-4670-b0c8-1b02194d3107
-- title:
--   The q-scale function vanishes at the origin for a spectrally negative Levy process with positive Gaussian coefficient and finite small-jump measure
-- statement:
--   Let X be a spectrally negative Levy process with a strictly positive Gaussian coefficient, let q > 0 and let W = W^{(q)} be its q-scale function, and suppose the Levy measure of X gives finite mass to the closed ray [-1, infinity). Then the scale function vanishes at the origin. This is the origin condition needed by the pointwise upgrade of the almost-everywhere q-harmonicity of the scale function to pointwise q-harmonicity, and it is the condition that the Laplace transform identity of the scale function forces once the Levy exponent grows faster than linearly. The proof uses the Proved quadratic lower bound psi_quadratic_lower_from_compensated_negative_jumps (97e86a26), which bounds X.psi(theta) below by X.c * theta + (X.sigma ^ 2 / 2) * theta ^ 2 minus the integral of y over the small jumps, and the fact that the quadratic term dominates because the Gaussian coefficient is positive. The finite mass of the Levy measure on [-1,1] is what makes the compensated small-jump integral a finite real number, and it is needed for the conclusion; the condition is not implied by the positivity of the Gaussian coefficient alone.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_zero_origin_gaussian_of_finite_small_jump_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤) :
    W 0 = 0 := by sorry

end AvramDividend.Classical
