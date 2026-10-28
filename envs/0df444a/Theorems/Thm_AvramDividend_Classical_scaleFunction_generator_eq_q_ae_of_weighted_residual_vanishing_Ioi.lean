-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_Ioi
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_Ioi
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-19T22:24:03.355037+00:00
-- url     : https://prove2.me/theorems/e65ef0d7-ea77-44ac-b844-d0f0ac527bff
-- title:
--   Almost-everywhere q-harmonicity of the scale function from vanishing weighted generator residual, on the positive half-line
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the whole positive half-line. Suppose further that for every real parameter theta with 0 <= theta and q < X.psi(theta), the theta-weighted integral of R over the positive half-line is integrable and vanishes: the integral of exp(-theta x) R(x) over x > 0 is zero. Then R vanishes almost everywhere on (0,a). This is the uniqueness step of the analytic core of Lemma 4 of Avram: the Laplace characterisation of the scale function gives the vanishing of the weighted residual, and a family of parameters, not a single one, identifies the residual itself. The proof splits the signed residual into its positive and negative parts, which are continuous and nonnegative, and applies Laplace uniqueness to that nonnegative pair. This statement carries continuity on the whole positive half-line, which is the hypothesis the nonnegative uniqueness theorem needs; continuity of the residual on compact subintervals of (0,a) alone is the separate obligation that upgrades the conclusion to the pointwise statement.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_Ioi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
