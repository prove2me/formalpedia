-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_C2
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T01:01:52.800726+00:00
-- url     : https://prove2.me/theorems/df35945e-da88-4c07-8de4-cf2c017e215b
-- title:
--   Q-harmonicity of the q-scale function below the optimal barrier in the C2 branch
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0, let W = W^{(q)} be its q-scale function and suppose c* > 0. Suppose the barrier candidate v_{c*} is C^2 on the barrier interval (0, c*) and the barrier normalisation factor is non-zero, so the scale function is C^2 there as well. Suppose that either the scale function vanishes at the origin or the Levy process has bounded variation, and suppose that the generator residual Gamma W - q W vanishes almost everywhere on (0, c*). Then the compensated jump integral of the generator of W converges at every point of (0, c*), and the residual vanishes at every point of (0, c*). This is the C^2 branch of the q-harmonicity of the scale function below the optimal barrier, which is the analytic core of Lemma 4 of Avram: the jump-integrability is supplied by the C^2 regularity of the scale function below the barrier, and the pointwise harmonicity by the continuity of the generator residual together with its almost-everywhere vanishing. The two remaining branches of the smoothing disjunction, the Gaussian case and the bounded-variation case, need regularity of the scale function itself, which is the separate obligation scaleFunction_contDiffOn_two_of_sigma_pos and scaleFunction_contDiffOn_one_of_boundedVariation.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W below the optimal barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_q_harmonic_of_nonzero_factor_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
