-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:26:47.745721+00:00
-- url     : https://prove2.me/theorems/d90e9d76-f92b-4b0a-9eea-a63578ac2d8b
-- title:
--   Pointwise q-harmonicity of the scale function below the optimal barrier in the prescribed C2 branch
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Suppose the barrier level c* is positive, that the barrier value v_{c*} is twice continuously differentiable on (0, c*), that the normalisation factor k = divE 1 (scaleDeriv W (cstar W).toReal) is non-zero, and that either W vanishes at the origin or X has bounded variation. Suppose that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of the generator residual over the positive half-line is integrable and vanishes. Then for every x in (0, c*) the compensated Levy generator jump integral of W converges and the generator residual vanishes there: (Gamma - q) W(x) = 0. This is the third smoothness branch of the core analytic obligation of Lemma 4 of Avram, the branch in which the C2 regularity of the barrier value is prescribed rather than derived. The proof composes three Proved results: the Proved theorem scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing (4dc30ca6), which identifies the residual almost everywhere from the vanishing of its weighted Laplace transform; the Proved theorem scaleFunction_generator_eq_q_ae_of_ae_harmonic_C2_nonzero (93e0ac7d), which upgrades the almost-everywhere vanishing to pointwise vanishing; and the Proved theorem scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar (00e5abc9), which supplies the convergence of the generator jump integral.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W on (0, c*), and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
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
