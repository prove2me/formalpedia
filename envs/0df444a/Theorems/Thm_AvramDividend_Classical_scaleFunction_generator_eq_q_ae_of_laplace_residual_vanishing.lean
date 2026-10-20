-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T22:29:30.953309+00:00
-- url     : https://prove2.me/theorems/b4d10133-4269-40b5-84eb-bc6364447f3a
-- title:
--   Almost-everywhere q-harmonicity of the scale function from vanishing of the Laplace transform of the generator residual
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function, and let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the whole positive half-line, and suppose that for every real parameter theta greater than some fixed b the theta-weighted integral of R over the positive half-line is integrable and vanishes. Then R vanishes almost everywhere on (0,a); in fact R vanishes everywhere on the positive half-line. This is the uniqueness step of the analytic core of Lemma 4 of Avram: the Laplace characterisation of the scale function gives the vanishing of the weighted residual, and a family of parameters, not a single one, identifies the residual itself. The proof splits the signed residual into its positive and negative parts, which are continuous and nonnegative, and applies Laplace uniqueness to that nonnegative pair. The separate obligation that the admissible parameters of the scale-function Laplace identity contain a whole half-line, that is that the Levy exponent X.psi tends to +infinity, supplies the hypothesis of this statement from the analytic side.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (b : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
