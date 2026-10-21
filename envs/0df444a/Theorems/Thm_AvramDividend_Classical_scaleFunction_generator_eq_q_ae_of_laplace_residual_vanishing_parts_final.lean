-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts_final
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts_final
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T02:14:00.721755+00:00
-- url     : https://prove2.me/theorems/e94dc166-4076-446d-9866-640065671c6a
-- title:
--   Almost-everywhere q-harmonicity of the scale function from agreement of the weighted transforms of the two parts of the generator residual
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function, and let a > 0. Suppose the generator residual R(x) = Gamma W(x) - q W(x) is continuous on the whole positive half-line. Suppose that for every real parameter theta greater than some fixed b the two weighted transforms of the positive part max(R, 0) and of the negative part max(-R, 0) of the residual are integrable over the positive half-line, and agree. Then R vanishes almost everywhere on (0,a). This is the uniqueness step of the analytic core of Lemma 4 of Avram: the residual is signed, so the uniqueness theorem for the Laplace transform of nonnegative functions is applied to its positive and negative parts separately. The two parts are continuous and nonnegative on the positive half-line, and the weighted transform of the residual vanishing is exactly the agreement of their weighted transforms. The conclusion is stated with the measure written explicitly, so that the almost-everywhere statement is at the measurable space of the measure.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts_final
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (b : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hpart : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0)) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
