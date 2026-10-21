-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_of_smooth
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_of_smooth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:10:32.833216+00:00
-- url     : https://prove2.me/theorems/e204b8c5-65e8-48b4-bf21-577f73e6a8a2
-- title:
--   Pointwise q-harmonicity of the scale function below the optimal barrier for a twice continuously differentiable scale function
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function. Suppose the barrier level c* is positive, that the scale function is twice continuously differentiable on the positive half-line, that the normalisation factor k = divE 1 (scaleDeriv W (cstar W).toReal) is non-zero, that the generator residual is continuous on the positive half-line, that for every admissible Laplace parameter theta the theta-weighted integral of the residual over the positive half-line is integrable and vanishes, and that either the scale function vanishes at the origin or X has bounded variation. Then for every x in (0, c*) the compensated Levy generator jump integral of W converges and the generator residual vanishes there: (Gamma - q) W(x) = 0. This is the common part of the three smoothness branches of the core analytic obligation of Lemma 4 of Avram: the regularity of the scale function is what distinguishes the branches, and once it is given the argument is the same. The proof composes the Proved theorems scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing (4dc30ca6) for the almost-everywhere vanishing, scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero (93e0ac7d) for the upgrade to pointwise vanishing, scaleFunction_generatorIntegrable_of_contDiff_two (a977868a) for the convergence of the generator jump integral, scaledW_contDiffOn_two_of_W_contDiffOn_two_positive (d83d7dcf) and vcstar_eq_scaledW_le_cstar_of_support (8e85de2d) for the transfer of the regularity to the barrier value, and scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2 (a18b3e5c) in the bounded variation case.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W on (0, c*), and the argument proceeds by identifying the residual from its Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_of_smooth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0)
    (horigin : W 0 = 0 ∨ X.BoundedVariation) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
