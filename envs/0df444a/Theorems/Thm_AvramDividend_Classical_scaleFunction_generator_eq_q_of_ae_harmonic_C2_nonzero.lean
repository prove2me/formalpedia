-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:10:24.464896+00:00
-- url     : https://prove2.me/theorems/93e0ac7d-25bb-49f5-822b-965194cce3a0
-- title:
--   Pointwise q-harmonicity of the scale function below c* from almost-everywhere q-harmonicity and C2 regularity
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0 and let W = W^{(q)} be its q-scale function, and suppose c* > 0. Suppose the barrier candidate v_{c*} is C^2 on the barrier interval (0, c*) and the barrier normalisation factor is non-zero, so the scale function is C^2 on the same interval. Suppose that the generator residual Gamma W - q W vanishes almost everywhere on (0, c*), and suppose that either the scale function vanishes at the origin or the Levy process has bounded variation. Then the residual vanishes at every point of (0, c*). This is the pointwise upgrade of the almost-everywhere q-harmonicity of the scale function, which is the last step before the dividend candidate itself becomes q-harmonic below the optimal barrier.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies Gamma W = q W, and the argument proceeds by identifying the residual from its Laplace transform and upgrading almost-everywhere vanishing to pointwise vanishing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
