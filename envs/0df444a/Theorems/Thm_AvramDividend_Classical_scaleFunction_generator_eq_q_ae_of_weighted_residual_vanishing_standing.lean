-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:19:35.645+00:00
-- url     : https://prove2.me/theorems/4dc30ca6-5c62-4093-a499-e625ac1df8cb
-- title:
--   Almost-everywhere q-harmonicity of the scale function from the vanishing of the weighted generator residual under the standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function, and let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the whole positive half-line. Suppose that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of R over the positive half-line is integrable and vanishes. Then R vanishes almost everywhere on (0,a). This is the general uniqueness step of the analytic core of Lemma 4 of Avram: the Laplace characterisation of the scale function gives the vanishing of the weighted residual, and a family of parameters, not a single one, identifies the residual itself. The proof composes the Proved theorem scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing (b4d10133), which identifies the residual from the vanishing of its Laplace transform on a half-line of parameters, with the parameter bridge psi_eventually_gt_of_standing (1c25d564), which says that under the standing assumptions the admissible parameters contain a whole half-line.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
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
