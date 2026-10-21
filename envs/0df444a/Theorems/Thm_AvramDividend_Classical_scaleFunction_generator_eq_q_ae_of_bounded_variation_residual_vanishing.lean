-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_bounded_variation_residual_vanishing
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_bounded_variation_residual_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:54:52.498265+00:00
-- url     : https://prove2.me/theorems/0c9a3356-5cf5-4e89-b680-47d26aaf1e04
-- title:
--   Almost-everywhere q-harmonicity of the scale function in the bounded variation case from the vanishing of the weighted generator residual
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions and with bounded variation, let q > 0 and let W = W^{(q)} be its q-scale function, and let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the whole positive half-line. Suppose further that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of R over the positive half-line is integrable and vanishes. Then R vanishes almost everywhere on (0,a). This is the bounded variation case of the uniqueness step of the analytic core of Lemma 4 of Avram. The proof combines two Proved results: the Proved theorem scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing (b4d10133), which identifies the residual from the vanishing of its Laplace transform on a half-line of parameters, and the Proved theorem psi_eventually_gt_of_boundedVariation (e9a8e903), which says that for a process of bounded variation the Levy exponent eventually exceeds q, so that the admissible parameters contain a whole half-line. A single Laplace parameter does not identify the residual; a family of parameters does.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform. The bounded variation case of the parameter family is supplied by the Levy exponent exceeding q eventually, which holds for a process of bounded variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_bounded_variation_residual_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
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
