-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-19T22:13:26.314905+00:00
-- url     : https://prove2.me/theorems/36234eca-400e-4116-913e-a48042a43a4c
-- title:
--   Almost-everywhere q-harmonicity of the scale function from vanishing of the weighted generator residual
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the open interval (0,a). Suppose further that for every real parameter theta with 0 <= theta and q < X.psi(theta), the theta-weighted integral of R over the positive half-line is integrable and vanishes: the integral of exp(-theta x) R(x) over x > 0 is zero. Then R vanishes almost everywhere on (0,a). This is the uniqueness step of the analytic core of Lemma 4 of Avram: the Laplace characterisation of the scale function gives the vanishing of the weighted residual, and a family of parameters, not a single one, identifies the residual itself. The pointwise statement on (0,a) then follows from the already proved continuity upgrade of the residual.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
