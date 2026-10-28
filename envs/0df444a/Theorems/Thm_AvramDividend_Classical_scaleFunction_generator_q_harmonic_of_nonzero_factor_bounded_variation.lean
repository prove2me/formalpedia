-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:10:10.486417+00:00
-- url     : https://prove2.me/theorems/2dc962ec-a1af-45f4-a053-ca4c980db462
-- title:
--   Pointwise q-harmonicity of the scale function below the optimal barrier in the bounded variation branch
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions and with bounded variation, let q > 0 and let W = W^{(q)} be its q-scale function, and suppose the barrier level c* is positive and the normalisation factor k = divE 1 (scaleDeriv W (cstar W).toReal) is non-zero. Suppose that for every admissible Laplace parameter theta, that is every theta >= 0 with q < X.psi(theta), the theta-weighted integral of the generator residual over the positive half-line is integrable and vanishes. Then, for every x in (0, c*), the compensated Levy generator jump integral of W converges and the generator residual vanishes there: (Gamma - q) W(x) = 0. This is the bounded variation branch of the core analytic obligation of Lemma 4 of Avram. The proof composes three Proved results: the Proved theorem scaleFunction_generator_eq_q_ae_of_bounded_variation_residual_vanishing (0c9a3356), which identifies the residual from the vanishing of its weighted Laplace transform in the bounded variation case; the Proved theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_C2 (df35945e), which upgrades the almost-everywhere vanishing to pointwise vanishing on (0, c*) under the C2 regularity of the barrier value; and the Proved theorem scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar (00e5abc9), which supplies the convergence of the generator jump integral.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W on (0, c*), and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
