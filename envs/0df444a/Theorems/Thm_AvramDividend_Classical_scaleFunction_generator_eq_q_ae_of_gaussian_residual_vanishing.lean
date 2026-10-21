-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_gaussian_residual_vanishing
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_gaussian_residual_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:32:28.219699+00:00
-- url     : https://prove2.me/theorems/57b4c9a9-a056-48d4-b5be-33fc62e47ca2
-- title:
--   Almost-everywhere q-harmonicity of the scale function in the Gaussian case from vanishing weighted generator residual
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0, let W = W^{(q)} be its q-scale function and let a > 0. Assume the Gaussian coefficient is positive, sigma > 0, and assume the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the positive half-line. Suppose that for every real parameter theta with 0 <= theta and q < X.psi(theta) the theta-weighted integral of R over the positive half-line is integrable and vanishes. Then R vanishes almost everywhere on (0,a). This is the analytic core of Lemma 4 of Avram in the Gaussian case. The point is that a single Laplace parameter does not identify the residual: one needs a whole family of admissible parameters. Because the Gaussian coefficient is positive, the Levy exponent X.psi eventually exceeds every fixed discount rate, so the admissible parameters contain a half-line; the uniqueness theorem for the Laplace transform then applies to the positive and negative parts of the residual separately. This statement isolates the uniqueness step from the separate obligation that the weighted residual transform vanishes, which is the analytic content of the scale-function Laplace characterisation together with a justified Fubini over the jump integral.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_gaussian_residual_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hσ : 0 < X.σ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
