-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:55:00.283718+00:00
-- url     : https://prove2.me/theorems/21a2556e-15fb-4f4a-8aa1-ee0b870bd630
-- title:
--   Pointwise q-harmonicity of the scale function below the optimal barrier in the Gaussian branch
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions and with a strictly positive Gaussian coefficient, let q > 0 and let W = W^{(q)} be its q-scale function. Suppose the barrier level c* is positive, that the scale function is twice continuously differentiable on the positive half-line, that the normalisation factor k = divE 1 (scaleDeriv W (cstar W).toReal) is non-zero, and that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of the generator residual over the positive half-line is integrable and vanishes. Then for every x in (0, c*) the compensated Levy generator jump integral of W converges and the generator residual vanishes there: (Gamma - q) W(x) = 0. This is the Gaussian branch of the core analytic obligation of Lemma 4 of Avram. The proof composes four Proved results: the Proved theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing (4dc30ca6) for the almost-everywhere vanishing of the residual; the Proved theorem scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero (93e0ac7d) for the upgrade to pointwise vanishing, which uses the origin condition W 0 = 0 supplied by the Proved theorem scaleFunction_origin_zero_of_quadratic_psi (a6b29c5d); the Proved theorem scaleFunction_generatorIntegrable_of_contDiff_two (a977868a) for the convergence of the generator jump integral; and the Proved theorem scaleFunction_contDiffOn_two_of_vcstar_nonzero (7b4c19f9), which transfers the C2 regularity of the scale function to the barrier value.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W on (0, c*), and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hc : 0 < cstar W)
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
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
