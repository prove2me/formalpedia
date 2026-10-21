-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_bounded_variation
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_bounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:44:52.028433+00:00
-- url     : https://prove2.me/theorems/6981f1ca-962d-4324-b4bf-d834fc45efa5
-- title:
--   Pointwise q-harmonicity of the scale function below the optimal barrier in the prescribed C2 branch for a process of bounded variation
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions and with bounded variation, let q > 0 and let W = W^{(q)} be its q-scale function. Suppose the barrier level c* is positive, that the barrier value v_{c*} is twice continuously differentiable on (0, c*), that the normalisation factor k = divE 1 (scaleDeriv W (cstar W).toReal) is non-zero, and that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of the generator residual over the positive half-line is integrable and vanishes. Then for every x in (0, c*) the compensated Levy generator jump integral of W converges and the generator residual vanishes there: (Gamma - q) W(x) = 0. This is the bounded variation case of the third smoothness branch of the core analytic obligation of Lemma 4 of Avram, the branch in which the C2 regularity of the barrier value is prescribed and the process additionally has bounded variation. The proof composes four Proved results: the Proved theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing (4dc30ca6) for the almost-everywhere vanishing of the residual; the Proved theorem scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2 (a18b3e5c) for the pointwise vanishing, which needs only bounded variation rather than the alternative W 0 = 0 or bounded variation; the Proved theorem scaleFunction_contDiffOn_two_of_vcstar_nonzero (7b4c19f9), which transfers the prescribed C2 regularity of the barrier value to the scale function; and the Proved theorem scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one (19029a99), which supplies the convergence of the generator jump integral.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W on (0, c*), and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
